import Langlands.AlgebraicGeometry.ClosedFibreAffineAlgebra
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual affine section maps under generic base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (U : X.Opens)

/-- The actual section map equips generic sections with their total-section
algebra structure. -/
@[instance_reducible]
def pullbackSectionAlgebra : Algebra Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
  (q.app U).hom.toAlgebra

variable {R : Type u} [CommRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : X ⟶ Spec (CommRingCat.of R)) (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))

include K s H in
/-- Over an affine total open, the actual section map of the actual generic
base change is localization at the non-zero-divisor base scalars. -/
theorem isLocalization_pullbackSectionAlgebra (hU : IsAffineOpen U) :
    letI := affineSectionAlgebra p hU
    letI := pullbackSectionAlgebra q U
    IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U) R⁰) Γ(Y, q ⁻¹ᵁ U) := by
  let := affineSectionAlgebra p hU
  let := pullbackSectionAlgebra q U
  have : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance :
      IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  have hV : IsAffineOpen (q ⁻¹ᵁ U) := hU.preimage q
  let f := Spec.homEquiv (hU.fromSpec ≫ p)
  let t := Spec.homEquiv (hV.fromSpec ≫ s)
  let : Algebra K Γ(Y, q ⁻¹ᵁ U) := t.hom.toAlgebra
  let : Algebra R Γ(Y, q ⁻¹ᵁ U) :=
    ((q.app U).hom.comp f.hom).toAlgebra
  have ht : Spec.map t = hV.fromSpec ≫ s :=
    Spec.homEquiv.symm_apply_apply _
  have hf : Spec.map f = hU.fromSpec ≫ p :=
    Spec.homEquiv.symm_apply_apply _
  have hmap : Spec.map (q.app U) ≫ hU.fromSpec = hV.fromSpec ≫ q := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec q hU hV le_rfl)
  have Hr : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ s) (U.ι ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (isPullback_morphismRestrict q U).paste_vert H
  have HS : IsPullback (Spec.map (q.app U)) (Spec.map t) (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    apply Hr.of_iso' hV.isoSpec.symm hU.isoSpec.symm (Iso.refl _) (Iso.refl _)
    · apply (cancel_mono U.ι).mp
      simpa only [Iso.symm_hom, Category.assoc, morphismRestrict_ι,
        IsAffineOpen.fromSpec] using hmap.symm
    · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, IsAffineOpen.fromSpec,
        Category.assoc] using ht.symm
    · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, IsAffineOpen.fromSpec,
        Category.assoc] using hf.symm
    · simp
  have HP : IsPushout f (CommRingCat.ofHom (algebraMap R K)) (q.app U) t := by
    have HOP : IsPullback (q.app U).op t.op f.op
        (CommRingCat.ofHom (algebraMap R K)).op :=
      IsPullback.of_map_of_faithful Scheme.Spec HS
    exact HOP.unop.flip
  have : IsScalarTower R Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R K Γ(Y, q ⁻¹ᵁ U) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom HP.w
  have : Algebra.IsPushout R Γ(X, U) K Γ(Y, q ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp HP
  exact (Algebra.isLocalization_iff_isPushout R⁰ K).mpr inferInstance

end Langlands.AlgebraicGeometry
