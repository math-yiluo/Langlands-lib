import Langlands.GroupScheme.Descent.DisjointGroupAssembly
import Langlands.GroupScheme.AffineWeilPiBase
import Langlands.GroupScheme.RelativeLevi.GeometricFiberComparison
import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Mathlib.RingTheory.Etale.Pi

/-! # A finite family as an actual affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffineWeil.FiniteFamily

variable (A : Type u) [CommRing A] (I : Type u) [Finite I]

/-- The component inclusion in the spectrum of the product algebra. -/
abbrev component (i : I) :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (I → A)) :=
  Spec.map (CommRingCat.ofHom (PiBase.evaluation A I i).toRingHom)

instance : IsIso (Sigma.desc (component A I)) := by
  change IsIso (sigmaSpec (fun _ : I => CommRingCat.of A))
  infer_instance

/-- The product algebra is finite, projective and étale over the original ring. -/
theorem algebra_properties :
    Module.Finite A (I → A) ∧ Module.Projective A (I → A) ∧
      Algebra.Etale A (I → A) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

omit [Finite I] in
/-- Every component is a section of the original spectrum map. -/
theorem component_baseMap (i : I) :
    component A I i ≫ algebraBaseMap A (I → A) = 𝟙 _ := by
  dsimp [component, algebraBaseMap]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

omit [Finite I] in
/-- A nonempty finite family gives a surjective spectrum map, over every ring. -/
theorem surjective_baseMap [Nonempty I] :
    Surjective (algebraBaseMap A (I → A)) := by
  constructor
  intro s
  let i : I := Classical.choice inferInstance
  refine ⟨component A I i s, ?_⟩
  change (component A I i ≫ algebraBaseMap A (I → A)) s = s
  rw [component_baseMap]
  rfl

variable (H : I → GroupScheme (Spec (CommRingCat.of A)))

/-- The actual group over the spectrum of the product ring assembled from the family. -/
abbrev group : GroupScheme (Spec (CommRingCat.of (I → A))) :=
  Descent.DisjointGroupAssembly.group (component A I) H

/-- Evaluation of the assembled group recovers the original component as a group scheme. -/
def componentIso (i : I) : (baseChange (component A I i)).obj (group A I H) ≅ H i :=
  Descent.DisjointGroupAssembly.componentIso (component A I) H i

/-- The underlying relative scheme is the actual disjoint union over the product base. -/
def underlyingIso : (group A I H).X ≅
    Over.mk (Sigma.desc fun i => (H i).X.hom ≫ component A I i) :=
  Descent.DisjointGroupAssembly.underlyingIso (component A I) H

instance [∀ i, IsAffine (H i).X.left] : IsAffine (group A I H).X.left :=
  inferInstanceAs (IsAffine
    (Descent.DisjointGroupAssembly.group (component A I) H).X.left)

instance [∀ i, LocallyOfFiniteType (H i).X.hom] :
    LocallyOfFiniteType (group A I H).X.hom := by
  have : LocallyOfFiniteType (Sigma.desc fun i => (H i).X.hom ≫ component A I i) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  rw [← Over.w (underlyingIso A I H).hom]
  change LocallyOfFiniteType ((underlyingIso A I H).hom.left ≫
    Sigma.desc fun i => (H i).X.hom ≫ component A I i)
  let : IsIso (underlyingIso A I H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (underlyingIso A I H).hom))
  infer_instance

/-- Smoothness of the structural map follows componentwise. -/
theorem smooth (hH : ∀ i, Smooth (H i).X.hom) : Smooth (group A I H).X.hom := by
  let : ∀ i, Smooth (H i).X.hom := hH
  have : Smooth (Sigma.desc fun i => (H i).X.hom ≫ component A I i) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  rw [← Over.w (underlyingIso A I H).hom]
  change Smooth ((underlyingIso A I H).hom.left ≫
    Sigma.desc fun i => (H i).X.hom ≫ component A I i)
  let : IsIso (underlyingIso A I H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (underlyingIso A I H).hom))
  infer_instance

/-- Any field-group property invariant under isomorphism and reflected by
field extension passes from all original geometric fibres to the assembled group. -/
theorem geometricFiber_property
    (P : ∀ (k : Type u) [Field k], GroupScheme (Spec (CommRingCat.of k)) → Prop)
    (hIso : ∀ (k : Type u) [Field k]
      {G G' : GroupScheme (Spec (CommRingCat.of k))}, (G ≅ G') → P k G' → P k G)
    (hField : ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
      (G : GroupScheme (Spec (CommRingCat.of k))),
      P K ((baseChange (algebraBaseMap k K)).obj G) → P k G)
    (hH : ∀ i, ∀ s : Spec (CommRingCat.of A),
      P _ (geometricFiber (H i) s)) :
    ∀ s : Spec (CommRingCat.of (I → A)), P _ (geometricFiber (group A I H) s) := by
  intro s
  obtain ⟨i, t, rfl⟩ := Descent.DisjointComponents.component_covers (component A I) s
  let b := component A I i
  let k := (Spec (CommRingCat.of (I → A))).residueField (b t)
  let K := (Spec (CommRingCat.of A)).residueField t
  let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have hlocal : P _ (geometricFiber ((baseChange b).obj (group A I H)) t) :=
    hIso _ ((baseChange (geometricPoint _ t)).mapIso (componentIso A I H i)) (hH i t)
  have hext : P _ ((baseChange (algebraBaseMap (AlgebraicClosure k)
      (AlgebraicClosure K))).obj (geometricFiber (group A I H) (b t))) :=
    hIso _ ((RelativeLevi.geometricFiberBaseChangeIso b t).app (group A I H)) hlocal
  exact hField _ _ _ hext

/-- Reductivity is inherited from all the original component groups. -/
theorem isReductive (hH : ∀ i, IsReductive (H i)) : IsReductive (group A I H) := by
  let : ∀ i, IsAffine (H i).X.left :=
    fun i => @isAffine_of_isAffineHom _ _ (H i).X.hom (hH i).isAffineHom inferInstance
  refine ⟨smooth A I H (fun i => (hH i).smooth), inferInstance, ?_⟩
  intro s
  have hc := geometricFiber_property A I H
    (fun _ _ G => IsConnectedReductive G)
    (fun _ _ _ _ e h => h.of_iso e)
    (fun _ _ _ _ _ _ h => IsConnectedReductive.of_fieldExtension h)
    (fun i t => ((hH i).geometricFiber t).isConnectedReductive_of_isAlgClosed) s
  exact hc.isPseudoReductive

/-- Adjoint geometric fibres are inherited from the component groups. -/
theorem isFibrewiseAdjoint (hH : ∀ i, IsFibrewiseAdjoint (H i)) :
    IsFibrewiseAdjoint (group A I H) :=
  geometricFiber_property A I H (fun _ _ G => IsAdjoint G)
    (fun _ _ _ _ e h => h.of_iso e)
    (fun _ _ _ _ _ _ h => IsAdjoint.of_fieldExtension h) hH

/-- Almost-simple geometric fibres are inherited from the component groups. -/
theorem isFibrewiseAlmostSimple
    (hH : ∀ i, ∀ s : Spec (CommRingCat.of A), IsAlmostSimple (geometricFiber (H i) s)) :
    ∀ s : Spec (CommRingCat.of (I → A)), IsAlmostSimple (geometricFiber (group A I H) s) :=
  geometricFiber_property A I H (fun _ _ G => IsAlmostSimple G)
    (fun _ _ _ _ e h => h.of_iso e)
    (fun _ _ _ _ _ _ h => IsAlmostSimple.of_fieldExtension h) hH

variable [∀ i, IsAffine (H i).X.left] [∀ i, LocallyOfFiniteType (H i).X.hom]

/-- The original finite product is the actual affine Weil restriction of
the assembled group over the finite product ring. -/
def iso : GroupScheme.pi H ≅ AffineWeil.groupScheme A (I → A) (group A I H) :=
  (Pi.mapIso (fun i => (componentIso A I H i).symm)) ≪≫
    (PiBase.iso A I (group A I H)).symm

end Langlands.GroupScheme.AffineWeil.FiniteFamily
