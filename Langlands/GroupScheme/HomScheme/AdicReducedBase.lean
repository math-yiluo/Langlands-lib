import Langlands.GroupScheme.HomScheme.AdicEffectivityFromFirstQuotient
import Langlands.GroupScheme.HomScheme.AdicSystemBaseChange
import Langlands.GroupScheme.HomScheme.InfinitesimalCohomologyReduction
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Adic Hom effectivity across nilpotent base reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]

private theorem ker_le_maximalIdeal (φ : A →+* B)
    (hφ : IsNilpotent (RingHom.ker φ)) : RingHom.ker φ ≤ maximalIdeal A := by
  intro x hx
  obtain ⟨n, hn⟩ := hφ
  have hnil : IsNilpotent x := ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
  exact nilpotent_iff_mem_prime.mp hnil _ inferInstance

/-- A nilpotent quotient induces an isomorphism on the first adic test. -/
theorem isIso_quotientSpecMap_zero_of_surjective (φ : A →+* B)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) :
    IsIso (quotientSpecMap φ (maximalIdeal A) 0) := by
  have hcomap : ((maximalIdeal A).map φ).comap φ = maximalIdeal A := by
    rw [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (ker_le_maximalIdeal φ hnil)]
  have hle : (((maximalIdeal A).map φ) ^ (0 + 1)).comap φ ≤ maximalIdeal A ^ (0 + 1) := by
    rw [zero_add, pow_one, pow_one, hcomap]
  let q := quotientRingMap φ (maximalIdeal A) 0
  have hq : Function.Bijective q :=
    ⟨Ideal.quotientMap_injective' hle, Ideal.quotientMap_surjective hφ⟩
  let e := (RingEquiv.ofBijective q hq).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom q) := inferInstanceAs (IsIso e.hom)
  unfold quotientSpecMap
  infer_instance

/-- The first-quotient comparison is an isomorphism of actual test schemes
over the original affine base. -/
def firstQuotientIsoOfNilpotentSurjection (φ : A →+* B)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) :
    (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
      (Over.mk (quotientMap ((maximalIdeal A).map φ) 0)) ≅
        Over.mk (quotientMap (maximalIdeal A) 0) := by
  let a := quotientOver φ (maximalIdeal A) 0
  have : IsIso ((Over.forget _).map a) := isIso_quotientSpecMap_zero_of_surjective φ hφ hnil
  have : IsIso a := isIso_of_reflects_iso a (Over.forget _)
  exact asIso a

variable {H G : GroupScheme (Spec (CommRingCat.of A))} [Smooth G.X.hom]

private theorem infinitesimalLift : MultiplicativeTypeInfinitesimalLiftStatement.{u} :=
  multiplicativeTypeInfinitesimalLift_of_cohomology
    Cohomology.multiplicativeTypeLowDegreeVanishing squareZeroHomomorphismCohomology
    (fun _ _ h => h.flat) (fun _ _ h => h.isAffineHom)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- An actual lift of the first quotient after a nilpotent base reduction
gives such a lift before reduction. -/
theorem hasFirstQuotientLift_of_nilpotent_pull
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (s : System (maximalIdeal A) H G) (φ : A →+* B)
    (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (f₀ : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj H ⟶
      (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)
    (hf₀ : (System.restrict ((maximalIdeal A).map φ) _ _ f₀).hom 0 =
      (s.pull φ).hom 0) :
    HasFirstQuotientLift s := by
  obtain ⟨f, hf⟩ := (infinitesimal_lifting_of_surjection infinitesimalLift φ hφ hnil H G hH).1 f₀
  refine ⟨f, ?_⟩
  let m := maximalIdeal A
  let fSystem := System.restrict m H G f
  have hPulled : (fSystem.pull φ).hom 0 = (s.pull φ).hom 0 := by
    rw [System.pull_restrict, hf]
    exact hf₀
  apply (evaluate_iso_bijective (H := H) (G := G)
    (firstQuotientIsoOfNilpotentSurjection φ hφ hnil)).1
  change evaluate (quotientOver φ m 0) (fSystem.hom 0) =
    evaluate (quotientOver φ m 0) (s.hom 0)
  rw [← System.flatten_pull_hom, ← System.flatten_pull_hom, hPulled]

end Langlands.GroupScheme.HomScheme.Adic
