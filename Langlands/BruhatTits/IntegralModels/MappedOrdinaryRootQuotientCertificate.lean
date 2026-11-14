import Langlands.BruhatTits.IntegralModels.IntegralRootReduction
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction

/-! # Ordinary roots detected after a group morphism and integral reduction -/

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
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K H}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : Kˣ → ℝ} (C : KPApartmentData i ω) (f : G ⟶ H)
    (T : IntegralTorusData D S (i ≫ f)) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D)
    {a : relativeRoots i} {ψ : C.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm i a)
    (hintegral : (C.affineRootGroup a ψ).map (rationalPoints.map f) ≤
      D.neutral.integralPoints)
    (hstrict : ∀ z : D.neutral.integralSections,
      D.neutral.integralPointMap z ∈
        (C.affineRootGroupPlus a ψ).map (rationalPoints.map f) →
          Q.reductiveReduction z = 1)
    (x : D.neutral.integralSections)
    (hx : D.neutral.integralPointMap x ∈
      (C.affineRootGroup a ψ).map (rationalPoints.map f))
    (houtside : Q.reductiveReduction x ∉
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (2 • T.characterSpecialization hT a.val)).carrier _)

include hlin hintegral hstrict hx houtside in
/-- Quotient exclusion after a group morphism certifies the original
ordinary affine root, with whole-depth integrality and strict-depth vanishing. -/
theorem mem_affineRoots_of_mapped_quotient_exclusion : ψ ∈ C.affineRoots := by
  classical
  refine ⟨a, hlin, ?_⟩
  intro hsub
  obtain ⟨x₀, hx₀, hx₀eq⟩ := hx
  obtain ⟨v, hv, w, hw, hvw⟩ := hsub hx₀
  change v * w = x₀ at hvw
  change w ∈ doubleRootGroupPoints i a.val at hw
  have hfvw : rationalPoints.map f v * rationalPoints.map f w =
      D.neutral.integralPointMap x := by
    rw [← map_mul, hvw]
    exact hx₀eq
  by_cases h2a : 2 • (a : characterLattice S) ∈ relativeRoots i
  · have hwroot : w ∈ rootGroupPoints i (2 • (a : characterLattice S)) := by
      rw [doubleRootGroupPoints, ite_eq_left h2a] at hw
      exact hw
    have hfwroot : rationalPoints.map f w ∈
        rootGroupPoints (i ≫ f) (2 • (a : characterLattice S)) :=
      RelativeRoot.comp_mem_subgroup i _ f hwroot
    obtain ⟨y, hy⟩ := hintegral ⟨v, C.affineRootGroupPlus_le a ψ hv, rfl⟩
    let z : D.neutral.integralSections := y⁻¹ * x
    have hz : D.neutral.integralPointMap z = rationalPoints.map f w := by
      dsimp only [z]
      rw [map_mul, map_inv, hy, ← hfvw, inv_mul_cancel_left]
    have hzroot : D.neutral.integralPointMap z ∈
        rootGroupPoints (i ≫ f) (2 • (a : characterLattice S)) := hz ▸ hfwroot
    have hqz := T.quotient_reduction_mem_rootFunctor hT Q
      (2 • (a : characterLattice S)) h2a.1 z hzroot
    rw [map_nsmul] at hqz
    have hyone : Q.reductiveReduction y = 1 :=
      hstrict y ⟨v, hv, hy.symm⟩
    have hqzx : Q.reductiveReduction z = Q.reductiveReduction x := by
      dsimp only [z]
      rw [map_mul, map_inv, hyone, inv_one, one_mul]
    exact houtside (hqzx ▸ hqz)
  · have hwone : w = 1 := by
      rw [doubleRootGroupPoints, ite_eq_right h2a] at hw
      exact Subgroup.mem_bot.mp hw
    have hxstrict : x₀ ∈ C.affineRootGroupPlus a ψ := by
      rw [hwone, mul_one] at hvw
      exact hvw ▸ hv
    apply houtside
    rw [hstrict x ⟨x₀, hxstrict, hx₀eq⟩]
    exact Subgroup.one_mem _

/-- The original ordinary affine root certified by quotient exclusion
after a group morphism; in particular the morphism may be conjugation. -/
def ordinaryRootOfMappedQuotientExclusion : C.affineRoots :=
  ⟨ψ, T.mem_affineRoots_of_mapped_quotient_exclusion C f hT Q hlin hintegral
    hstrict x hx houtside⟩

@[simp] theorem ordinaryRootOfMappedQuotientExclusion_coe :
    (T.ordinaryRootOfMappedQuotientExclusion C f hT Q hlin hintegral hstrict x hx
      houtside : C.Apartment →ᵃ[ℝ] ℝ) = ψ := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
