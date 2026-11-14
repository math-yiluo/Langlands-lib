import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Étale transport of relative Borel subgroups -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section AlgebraicFieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]
  {B G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : B ⟶ G}

/-- A geometric Borel remains geometric Borel over an algebraic field extension. -/
theorem IsGeometricBorelSubgroup.baseChange_of_algebraicExtension
    (hi : IsGeometricBorelSubgroup i) :
    IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) := by
  let b := algebraBaseMap k K
  let d := algebraicClosureBaseMap k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have : IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      ((algebraicClosureEmbedding k K).commutes x).symm
  have : Algebra.IsAlgebraic (AlgebraicClosure k) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := k) (AlgebraicClosure k)
  have : IsIso d := isIso_SpecMap_iff.mpr
    (IsAlgClosed.algebraMap_bijective_of_isIntegral :
      Function.Bijective (algebraMap (AlgebraicClosure k) (AlgebraicClosure K)))
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  apply isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    (hclosed := hi.1.isClosedSubgroup.baseChange b)
  let E := algebraicClosureBaseChangeIso k K
  have h := ((hi.2.baseChange_of_isIso d).iso_comp (E.app B).symm).comp_iso (E.app G)
  change IsBorelSubgroup
    (((E.app B).inv ≫ (GroupScheme.baseChange d).map
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map i)) ≫ (E.app G).hom) at h
  rw [Category.assoc, algebraicClosureBaseChangeIso_hom_naturality,
    Iso.inv_hom_id_assoc] at h
  exact h

end AlgebraicFieldExtension

namespace RelativeLevi

/-- Geometric Borelness is unchanged by the comparison of iterated pullbacks. -/
theorem isGeometricBorelSubgroup_iterated_baseChange_iff
    {k : Type u} [Field k] {S T : Scheme.{u}}
    (f : T ⟶ S) (q : Spec (CommRingCat.of k) ⟶ T)
    (r : Spec (CommRingCat.of k) ⟶ S) (h : q ≫ f = r)
    {B G : GroupScheme S} (i : B ⟶ G) :
    IsGeometricBorelSubgroup ((GroupScheme.baseChange q).map
      ((GroupScheme.baseChange f).map i)) ↔
      IsGeometricBorelSubgroup ((GroupScheme.baseChange r).map i) := by
  constructor
  · intro hi
    have H := (hi.iso_comp (Descent.pullbackComparison f q r h B).symm).comp_iso
      (Descent.pullbackComparison f q r h G)
    change IsGeometricBorelSubgroup
      (((Descent.pullbackComparison f q r h B).inv ≫
        (GroupScheme.baseChange q).map ((GroupScheme.baseChange f).map i)) ≫
          (Descent.pullbackComparison f q r h G).hom) at H
    rw [Category.assoc, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc] at H
    exact H
  · intro hi
    have H := (hi.iso_comp (Descent.pullbackComparison f q r h B)).comp_iso
      (Descent.pullbackComparison f q r h G).symm
    change IsGeometricBorelSubgroup
      (((Descent.pullbackComparison f q r h B).hom ≫
        (GroupScheme.baseChange r).map i) ≫
          (Descent.pullbackComparison f q r h G).inv) at H
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at H
    exact H

/-- The fibre after base change is the scalar extension of the original fibre,
up to the actual pullback comparison. -/
theorem isGeometricBorelSubgroup_residueFiber_baseChange_iff
    {S T : Scheme.{u}} (b : T ⟶ S) {B G : GroupScheme S}
    (i : B ⟶ G) (x : T) :
    IsGeometricBorelSubgroup (residueFiberHom ((GroupScheme.baseChange b).map i) x) ↔
      IsGeometricBorelSubgroup ((GroupScheme.baseChange
        (Spec.map (b.residueFieldMap x))).map (residueFiberHom i (b x))) := by
  rw [isGeometricBorelSubgroup_iterated_baseChange_iff b (T.fromSpecResidueField x)
    (T.fromSpecResidueField x ≫ b) rfl]
  exact (isGeometricBorelSubgroup_iterated_baseChange_iff
    (S.fromSpecResidueField (b x)) (Spec.map (b.residueFieldMap x))
      (T.fromSpecResidueField x ≫ b)
        (b.SpecMap_residueFieldMap_fromSpecResidueField x) i).symm

end RelativeLevi

section EtaleBaseChange

variable {S T : Scheme.{u}} (b : T ⟶ S) [Etale b]
  {B G : GroupScheme S} [IsAffineHom G.X.hom] {i : B ⟶ G}

/-- Étale base change preserves the geometric Borel property on a residue fibre. -/
theorem IsGeometricBorelSubgroup.residueFiber_baseChange_of_etale (x : T)
    (hi : IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i (b x))) :
    IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom ((GroupScheme.baseChange b).map i) x) := by
  let : Algebra (S.residueField (b x)) (T.residueField x) :=
    (b.residueFieldMap x).hom.toAlgebra
  have : Algebra.IsSeparable (S.residueField (b x)) (T.residueField x) := inferInstance
  have : Algebra.IsAlgebraic (S.residueField (b x)) (T.residueField x) := inferInstance
  have : IsAffineHom
      ((GroupScheme.baseChange (S.fromSpecResidueField (b x))).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (S.fromSpecResidueField (b x))))
  apply (RelativeLevi.isGeometricBorelSubgroup_residueFiber_baseChange_iff b i x).mpr
  have H := hi.baseChange_of_algebraicExtension
    (k := S.residueField (b x)) (K := T.residueField x)
    (i := RelativeLevi.residueFiberHom i (b x))
  exact H

/-- For a closed fibre inclusion, an étale scalar extension reflects geometric Borelness. -/
theorem IsGeometricBorelSubgroup.of_residueFiber_baseChange_of_etale (x : T)
    (hi : IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom ((GroupScheme.baseChange b).map i) x))
    (hclosed : IsClosedSubgroup (RelativeLevi.residueFiberHom i (b x))) :
    IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i (b x)) := by
  let : Algebra (S.residueField (b x)) (T.residueField x) :=
    (b.residueFieldMap x).hom.toAlgebra
  have : Algebra.IsSeparable (S.residueField (b x)) (T.residueField x) := inferInstance
  have : Algebra.IsAlgebraic (S.residueField (b x)) (T.residueField x) := inferInstance
  have : IsAffineHom
      ((GroupScheme.baseChange (S.fromSpecResidueField (b x))).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (S.fromSpecResidueField (b x))))
  exact IsGeometricBorelSubgroup.of_baseChange_of_algebraicExtension
    (k := S.residueField (b x)) (K := T.residueField x)
    (i := RelativeLevi.residueFiberHom i (b x))
    ((RelativeLevi.isGeometricBorelSubgroup_residueFiber_baseChange_iff b i x).mp hi) hclosed

/-- A relative Borel remains a relative Borel after an étale base change. -/
theorem IsRelativeBorelSubgroup.baseChange_of_etale
    (hi : IsRelativeBorelSubgroup i) :
    IsRelativeBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  have : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  have : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  have : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  have hgeo := fun x : T =>
    (hi.residueFiber (b x)).residueFiber_baseChange_of_etale b x
  exact
    { isRelativeParabolicSubgroup :=
        { smooth := inferInstanceAs (Smooth (pullback.snd B.X.hom b))
          isAffineHom := MorphismProperty.pullback_snd B.X.hom b
            hi.isRelativeParabolicSubgroup.isAffineHom
          mono := Functor.map_mono (Over.pullback b) i.hom.hom
          residueFiber := fun x => (hgeo x).isParabolicSubgroup }
      residueFiber := hgeo }

end EtaleBaseChange

namespace RelativeLevi

/-- Smoothness can be checked after pulling back to a small étale cover of the base. -/
theorem smooth_of_etale_cover_pullbacks {S X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (g : X ⟶ S)
    (hsm : ∀ a, Smooth (pullback.snd g (𝒰.f a))) : Smooth g := by
  let 𝒱 := 𝒰.pullback₁ g
  let p := Sigma.desc 𝒱.f
  have : Etale p := IsZariskiLocalAtSource.sigmaDesc fun a => Scheme.Cover.map_prop 𝒱 a
  have : Surjective p := inferInstanceAs (Surjective (Sigma.desc 𝒱.f))
  have hcomp : ∀ a, Smooth (𝒱.f a ≫ g) := by
    intro a
    rw [← 𝒰.pullbackHom_map g a]
    have : Smooth (𝒰.pullbackHom g a) := hsm a
    have : Etale (𝒰.f a) := 𝒰.map_prop a
    infer_instance
  have heq : p ≫ g = Sigma.desc (fun a => 𝒱.f a ≫ g) := by
    apply Sigma.hom_ext
    intro a
    simp [p]
  have : Smooth (p ≫ g) := by
    rw [heq]
    exact IsZariskiLocalAtSource.sigmaDesc hcomp
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp p g

end RelativeLevi

/-- A supplied closed inclusion is relative Borel when it is so on an étale cover. -/
theorem IsRelativeBorelSubgroup.of_etale_cover
    {S : Scheme.{u}} {B G : GroupScheme S} [IsAffineHom G.X.hom] {i : B ⟶ G}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hclosed : IsClosedSubgroup i)
    (hi : ∀ a, IsRelativeBorelSubgroup ((GroupScheme.baseChange (𝒰.f a)).map i)) :
    IsRelativeBorelSubgroup i := by
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s) := by
    intro s
    obtain ⟨a, x, rfl⟩ := 𝒰.exists_eq s
    have : Etale (𝒰.f a) := 𝒰.map_prop a
    exact ((hi a).residueFiber x).of_residueFiber_baseChange_of_etale (𝒰.f a) x
      (hclosed.baseChange (S.fromSpecResidueField (𝒰.f a x)))
  have : IsClosedImmersion i.hom.hom.left := hclosed
  exact
    { isRelativeParabolicSubgroup :=
        { smooth := RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰 B.X.hom
            (fun a => (hi a).isRelativeParabolicSubgroup.smooth)
          isAffineHom := by
            rw [← Over.w i.hom.hom]
            infer_instance
          mono := Over.mono_of_mono_left _
          residueFiber := fun s => (hgeo s).isParabolicSubgroup }
      residueFiber := hgeo }

section PresentationTransport

variable {S : Scheme.{u}} {B B' G G' : GroupScheme S} {i : B ⟶ G}

end PresentationTransport

end Langlands.GroupScheme
