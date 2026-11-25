/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeCriterion
import WeilConjectures.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison
import WeilConjectures.AlgebraicGeometry.TensorCounitOneKFlatCoordinates

/-! # Derived base change for a bounded relatively flat complex

Source: Stacks Project, perfect.tex, Lemma 36.26.4, Tag 0A1D
(blueprint: lem-pc-rf-base-change-complex).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section

namespace AlgebraicGeometry
open MonoidalCategory

private theorem tensor_cancel_iso {C : Type*} [Category C] [MonoidalCategory C]
    {A B U V : C} (e : A ≅ B) (c : U ⟶ V) :
    (e.inv ⊗ₘ 𝟙 U) ≫ (A ◁ c) ≫ (e.hom ⊗ₘ 𝟙 V) = B ◁ c := by
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom]
  simp

-- Naturality compares the derived adjunctions and composition isomorphisms.
private theorem baseChange_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {A B : schemeDerivedCategory X} (a : A ⟶ B) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g g' h B =
      schemeDerivedBaseChangeMap f f' g g' h A ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map a) := by
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f')
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f')
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f'))
  let c₁ := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) f' g)
  let c₂ := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) g' f)
  let d : derivedPullback (f' ≫ g) ≅ derivedPullback (g' ≫ f) :=
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm)
  let t : ∀ K : schemeDerivedCategory X,
      (derivedPullback f').obj ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj K)) ⟶ (derivedPullback g').obj K :=
    fun K ↦ c₁.hom.app ((schemeDerivedDirectImage f).obj K) ≫
      d.hom.app ((schemeDerivedDirectImage f).obj K) ≫
      c₂.inv.app ((schemeDerivedDirectImage f).obj K) ≫
      (derivedPullback g').map (adj.counit.app K)
  have hd (K : schemeDerivedCategory X) :
      d.hom.app ((schemeDerivedDirectImage f).obj K) =
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) := by
    exact eqToHom_app (congrArg (fun k ↦ derivedPullback k) h.symm) _
  have ht : (derivedPullback f').map
        ((derivedPullback g).map ((schemeDerivedDirectImage f).map a)) ≫ t B =
      t A ≫ (derivedPullback g').map a := by
    dsimp only [t]
    rw [← Functor.comp_map, c₁.hom.naturality_assoc,
      d.hom.naturality_assoc, c₂.inv.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp]
    rw [show (derivedPullback f).map ((schemeDerivedDirectImage f).map a) ≫
        adj.counit.app B = adj.counit.app A ≫ a from adj.counit.naturality a]
    simp only [Functor.map_comp, Category.assoc]
  have happ (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (t K) := by
    simp only [t, hd]
    rfl
  rw [happ A, happ B, ← adj'.homEquiv_naturality_left,
    ← adj'.homEquiv_naturality_right, ht]


-- Construct tensor-total coproducts directly, avoiding repeated colimit instance searches.
private theorem relativelyFlat_tensorHasMapBifunctor (X : Scheme.{u})
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor P G
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) := by
  intro n
  exact ((hasColimitsOfSizeShrink.{0, 0, u, u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).has_colimits_of_shape _).has_colimit _

private theorem relativelyFlat_isIso_transport
    {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {A B U V : D} (a : A ≅ B) (b : U ≅ V) (c : B ⟶ U) (t : A ⟶ V)
    {S T : C} (s : S ≅ T) (x : S ⟶ F.obj A) (y : T ⟶ F.obj B)
    (ht : a.hom ≫ c ≫ b.hom = t)
    (hn : s.hom ≫ y = x ≫ F.map a.hom)
    (h : IsIso (x ≫ F.map t)) : IsIso (y ≫ F.map c) := by
  have hcomp : IsIso ((s.hom ≫ (y ≫ F.map c)) ≫ F.map b.hom) := by
    simpa only [← ht, Functor.map_comp, Category.assoc, reassoc_of% hn] using h
  have : IsIso (s.hom ≫ (y ≫ F.map c)) :=
    (isIso_comp_right_iff _ (F.map b.hom)).mp hcomp
  exact IsIso.of_isIso_comp_left s.hom _

/-- The canonical base-change map for a relatively flat bounded-above complex is
invertible. `P` is a K-flat representative of `E` (`e`), so the total tensor complex
`Tot(P ⊗ G)` represents `E ⊗^L G`; `α` is any identification of the two (invertibility
does not depend on it, since it is precomposed after the derived functors). The map
displayed is `Lg^*Rf_*(E ⊗^L G) ⟶ Rf_{T,*}L(g')^*Tot(P ⊗ G) ⟶ Rf_{T,*}(g')^*Tot(P ⊗ G)`:
the recorded derived base-change map followed by the universal derived-to-ordinary
pullback counit `SingleComplexBaseChange.counit` at `Tot(P ⊗ G)`. Its target is the node's
`Rf_{T,*}(L(g')^*E ⊗^L (g')^*G)`: the termwise module pullback tensor isomorphism
(lem-weil-pbc-module-pullback-tensor) identifies `(g')^*Tot(P ⊗ G)` with
`Tot((g')^*P ⊗ (g')^*G)`, and `(g')^*P` is K-flat and represents `L(g')^*E`, so this
complex represents `L(g')^*E ⊗^L (g')^*G`. Under these identifications and the
derived pullback tensor comparison (lem-pc-derived-pullback-tensor-product, Stacks 079U)
the displayed map is the source's canonical map; postcomposing with these isomorphisms
does not change `IsIso`. No boundedness or flatness is imposed on `E`.
Source: Stacks Project, perfect.tex, Lemma 36.26.4, Tag 0A1D, lemma-base-change-tensor.
Proof (the three steps of the node):
1. Apply lem-pc-rf-base-change-single-complex-criterion (Tags 0DJ9 and 0DJA) to the
   qcqs morphism, `E` with quasi-coherent cohomology, and the bounded-above complex `G`.
2. Verify the criterion's stalk condition by
   lem-pc-derived-pullback-tor-independent-flat-complex: the stalk complex of `G` is
   bounded above and flat over the base stalk, so ordinary tensor with the new base
   computes derived tensor; the localization to the fibre-product stalk preserves it.
3. Substitute this condition into the criterion. Its canonical base-change map,
   followed by the derived-to-ordinary pullback counit, is invertible; transporting
   along `α` gives the displayed map.
(blueprint: lem-pc-rf-base-change-complex). -/
theorem relativelyFlat_derivedBaseChange_complex
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S)
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, Scheme.Modules.IsFlatOver (G.X i) f)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (e : DerivedCategory.Q.obj P ≅ E)
    (α : E ⊗ DerivedCategory.Q.obj G ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) :
    IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map α.hom) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        (cast (by rfl) ((SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))))) :
          (derivedPullback (pullback.fst f g)).obj
              (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
                (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ⟶
            DerivedCategory.Q.obj
              (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
                (.up ℤ)).obj (CochainComplex.mapBifunctor P G
                  (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))))) := by
  classical
  let := relativelyFlat_tensorHasMapBifunctor X P G
  simp only [cast_eq]
  let sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison (pullback.fst f g)
  have hstalk := SingleComplexBaseChange.counit_stalkCondition_of_localizedComparison
    f (pullback.snd f g) g (pullback.fst f g) sq G (by
      intro z
      let := SingleComplexBaseChange.leftAlgebra f (pullback.fst f g) z
      let := SingleComplexBaseChange.rightAlgebra f (pullback.snd f g) g
        (pullback.fst f g) sq z
      let := (SingleComplexBaseChange.tensorMap f (pullback.snd f g) g
        (pullback.fst f g) sq z).toAlgebra
      let := HasDerivedCategory.standard (ModuleCat.{u}
        (SingleComplexBaseChange.R f (pullback.fst f g) z))
      let := HasDerivedCategory.standard (ModuleCat.{u}
        (SingleComplexBaseChange.B (pullback.snd f g) z))
      apply derivedPullback_torIndependent_flat_complex g f G hbounded hqc hflat z
      · rfl
      · rfl
      · exact (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap
          f (pullback.snd f g) g (pullback.fst f g) sq z)).1
      · exact (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap
          f (pullback.snd f g) g (pullback.fst f g) sq z)).2)
  have hi := singleComplexBaseChangeCriterion f (pullback.snd f g) g
    (pullback.fst f g) sq E hE G hqc hstalk τ hτ
  obtain ⟨a₀, b₀, hab₀⟩ := tensorCounit_oneKFlat_coordinates
    (pullback.fst f g) P G hP τ hτ
  let a := tensorIso e.symm (Iso.refl (DerivedCategory.Q.obj G)) ≪≫ a₀
  let b := b₀ ≪≫ tensorIso ((derivedPullback (pullback.fst f g)).mapIso e)
    (Iso.refl _)
  have hab : (derivedPullback (pullback.fst f g)).map a.hom ≫
      (SingleComplexBaseChange.counit (pullback.fst f g)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫ b.hom =
      τ E (DerivedCategory.Q.obj G) ≫
        (derivedPullback (pullback.fst f g)).obj E ◁
          (SingleComplexBaseChange.counit (pullback.fst f g)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj G) := by
    simp only [a, b, Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    erw [reassoc_of% hab₀]
    rw [reassoc_of% (hτ.2 E (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj G) (DerivedCategory.Q.obj G) e.inv (𝟙 _))]
    simp only [CategoryTheory.Functor.map_id]
    exact congrArg (fun t ↦ τ E (DerivedCategory.Q.obj G) ≫ t)
      (tensor_cancel_iso ((derivedPullback (pullback.fst f g)).mapIso e)
        ((SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj G)))
  have hn := baseChange_naturality f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition a.hom
  have := relativelyFlat_isIso_transport (schemeDerivedDirectImage (pullback.snd f g))
    ((derivedPullback (pullback.fst f g)).mapIso a) b
    ((SingleComplexBaseChange.counit (pullback.fst f g)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))))) _
    ((derivedPullback g).mapIso ((schemeDerivedDirectImage f).mapIso a)) _ _ hab hn hi
  infer_instance

end AlgebraicGeometry
