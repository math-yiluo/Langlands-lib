import Langlands.GroupScheme.Reductive.AffinePinnedTestCentrality
import Mathlib.RingTheory.LocalProperties.Basic

/-! # Detecting pinning coefficients on local tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M : AffinePinnedModel.{u}}

local instance : Smooth M.group.X.hom := M.reductive.smooth

open Classical in
/-- The coefficient of the target chosen simple vector in the corresponding
weight projection of the image of a source chosen simple vector. -/
def pinningCoefficient (M : AffinePinnedModel.{u})
    (σ : CategoryTheory.Aut M.group) (s t : M.basis.support) : M.ring :=
  (M.pinning t).symm
    (splitTorus.exponentProjection M.coordinates M.group M.inclusion
      (M.rootDatum.root t)
      (Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val))

/-- When the entire image is a scalar multiple of the target vector, the
constructed projected coefficient is exactly that scalar. -/
theorem pinningCoefficient_of_vector_eq
    (σ : CategoryTheory.Aut M.group) {s t : M.basis.support} {c : M.ring}
    (hv : Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      c • (M.pinning t 1).val) :
    M.pinningCoefficient σ s t = c := by
  classical
  have hp := congrArg
    (fun v : splitTorus.exponentWeightSpace M.coordinates M.group M.inclusion
      (M.rootDatum.root t) => v.val)
    ((M.pinning t).map_smul (c : CommRingCat.of M.ring) (1 : CommRingCat.of M.ring))
  simp only [smul_eq_mul, mul_one, Submodule.coe_smul] at hp
  unfold pinningCoefficient
  rw [hv, ← hp, splitTorus.exponentProjection_subtype, LinearEquiv.symm_apply_apply]

/-- A comparison that permutes the chosen pinning vectors on all local tests
has scalar one whenever the image of an original vector is a scalar multiple
of another original vector. -/
theorem pinning_coefficient_eq_one_of_localPinning
    (σ : CategoryTheory.Aut M.group)
    (hpin : PreservesLocalPinning ((baseChange (𝟙 M.base)).mapIso σ.asIso))
    {s t : M.basis.support} {c : M.ring}
    (hv : Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      c • (M.pinning t 1).val) : c = 1 := by
  have hlocal (A : Type u) [CommRing A] [IsLocalRing A] [Algebra M.ring A] :
      algebraMap M.ring A c = 1 := by
    obtain ⟨p, hp⟩ := hpin A (algebraBaseMap M.ring A)
      (by simp only [Category.comp_id]) (by simp only [Category.comp_id])
    have hmap : ((baseChange (𝟙 M.base)).map σ.asIso.hom).hom.hom.left ≫
        pullback.fst M.group.X.hom (𝟙 M.base) =
      pullback.fst M.group.X.hom (𝟙 M.base) ≫ σ.asIso.hom.hom.hom.left := by
      change pullback.lift _ _ _ ≫ _ = _
      exact pullback.lift_fst _ _ _
    have he := congrArg
      (fun k => k ≫ pullback.fst M.group.X.hom (𝟙 M.base)) (hp s)
    change (M.rootVectorPoint (𝟙 M.base) A (algebraBaseMap M.ring A) _ s ≫
      ((baseChange (𝟙 M.base)).map σ.asIso.hom).hom.hom.left) ≫
        pullback.fst M.group.X.hom (𝟙 M.base) =
      M.rootVectorPoint (𝟙 M.base) A (algebraBaseMap M.ring A) _ (p s) ≫
        pullback.fst M.group.X.hom (𝟙 M.base) at he
    rw [Category.assoc, hmap, ← Category.assoc,
      rootVectorPoint_fst, rootVectorPoint_fst] at he
    have hLie : Lie.targetMapLinear σ.asIso.hom A
        (lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val) =
      lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning (p s) 1).val := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Over.OverMorphism.ext
      exact he
    have hcoeff := congrArg
      (lieKernelMapLinear M.group (Algebra.ofId M.ring A)) hv
    rw [← lieKernelTargetLinear_map, LinearMap.map_smulₛₗ] at hcoeff
    exact (M.simpleVectorAt_smul_eq A (hcoeff.symm.trans hLie)).2
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro P hP
  let : P.IsPrime := hP.isPrime
  simpa only [map_sub, map_one, sub_eq_zero] using hlocal (Localization.AtPrime P)

/-- Under local pinning, a supplied scalar-multiple vector equation is the
exact chosen-vector equation over the original coefficient ring. -/
theorem pinning_vector_eq_of_localPinning_of_scalar
    (σ : CategoryTheory.Aut M.group)
    (hpin : PreservesLocalPinning ((baseChange (𝟙 M.base)).mapIso σ.asIso))
    {s t : M.basis.support} {c : M.ring}
    (hv : Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      c • (M.pinning t 1).val) :
    Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      (M.pinning t 1).val := by
  rw [hv, pinning_coefficient_eq_one_of_localPinning σ hpin hv, one_smul]

/-- Local pinning makes the constructed coefficient one whenever the image
lies on the chosen target line with a supplied scalar equation. -/
theorem pinningCoefficient_eq_one_of_localPinning
    (σ : CategoryTheory.Aut M.group)
    (hpin : PreservesLocalPinning ((baseChange (𝟙 M.base)).mapIso σ.asIso))
    {s t : M.basis.support} {c : M.ring}
    (hv : Lie.targetMapLinear σ.asIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      c • (M.pinning t 1).val) : M.pinningCoefficient σ s t = 1 := by
  rw [pinningCoefficient_of_vector_eq σ hv,
    pinning_coefficient_eq_one_of_localPinning σ hpin hv]

end Langlands.GroupScheme.AffinePinnedModel
