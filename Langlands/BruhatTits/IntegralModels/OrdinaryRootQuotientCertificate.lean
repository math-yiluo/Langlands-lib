import Langlands.BruhatTits.IntegralModels.IntegralRootReduction
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction

/-! # Ordinary affine roots detected by actual quotient-root exclusion -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : Kˣ → ℝ} (C : KPApartmentData i ω)
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D)
    {a : relativeRoots i} {ψ : C.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm i a)
    (hintegral : C.affineRootGroup a ψ ≤ D.neutral.integralPoints)
    (hstrict : ∀ z : D.neutral.integralSections,
      D.neutral.integralPointMap z ∈ C.affineRootGroupPlus a ψ →
        Q.reductiveReduction z = 1)
    (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈ C.affineRootGroup a ψ)
    (houtside : Q.reductiveReduction x ∉
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (2 • T.characterSpecialization hT a.val)).carrier _)

include hlin hintegral hstrict hx houtside in
/-- If strict-depth sections vanish in the actual quotient, an integral
depth point outside its doubled residue root group certifies an ordinary root. -/
theorem mem_affineRoots_of_quotient_exclusion : ψ ∈ C.affineRoots := by
  classical
  refine ⟨a, hlin, ?_⟩
  intro hsub
  obtain ⟨v, hv, w, hw, hvw⟩ := hsub hx
  change v * w = D.neutral.integralPointMap x at hvw
  change w ∈ doubleRootGroupPoints i a.val at hw
  by_cases h2a : 2 • (a : characterLattice S) ∈ relativeRoots i
  · have hwroot : w ∈ rootGroupPoints i (2 • (a : characterLattice S)) := by
      rw [doubleRootGroupPoints, ite_eq_left h2a] at hw
      exact hw
    obtain ⟨y, hy⟩ := hintegral (C.affineRootGroupPlus_le a ψ hv)
    let z : D.neutral.integralSections := y⁻¹ * x
    have hz : D.neutral.integralPointMap z = w := by
      dsimp only [z]
      rw [map_mul, map_inv, hy, ← hvw, inv_mul_cancel_left]
    have hzroot : D.neutral.integralPointMap z ∈
        rootGroupPoints i (2 • (a : characterLattice S)) := hz ▸ hwroot
    have hqz := T.quotient_reduction_mem_rootFunctor hT Q
      (2 • (a : characterLattice S)) h2a.1 z hzroot
    rw [map_nsmul] at hqz
    have hyone : Q.reductiveReduction y = 1 := hstrict y (hy.symm ▸ hv)
    have hqzx : Q.reductiveReduction z = Q.reductiveReduction x := by
      dsimp only [z]
      rw [map_mul, map_inv, hyone, inv_one, one_mul]
    exact houtside (hqzx ▸ hqz)
  · have hwone : w = 1 := by
      rw [doubleRootGroupPoints, ite_eq_right h2a] at hw
      exact Subgroup.mem_bot.mp hw
    have hxstrict : D.neutral.integralPointMap x ∈
        C.affineRootGroupPlus a ψ := by
      rw [hwone, mul_one] at hvw
      exact hvw ▸ hv
    apply houtside
    rw [hstrict x hxstrict]
    exact Subgroup.one_mem _

/-- The original affine functional, certified ordinary by actual quotient
exclusion and the stated strict-depth kernel premise. -/
def ordinaryRootOfQuotientExclusion : C.affineRoots :=
  ⟨ψ, T.mem_affineRoots_of_quotient_exclusion C hT Q hlin hintegral
    hstrict x hx houtside⟩

@[simp] theorem ordinaryRootOfQuotientExclusion_coe :
    (T.ordinaryRootOfQuotientExclusion C hT Q hlin hintegral hstrict x hx houtside :
      C.Apartment →ᵃ[ℝ] ℝ) = ψ := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
