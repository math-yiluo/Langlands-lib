import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurTruncationBruhatCancellation

/-! # Pointwise idempotence of Arthur truncation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Group.RelativeWeylIndexing Langlands.Aubert.General.RationalPointFamily
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "B" => SimpleRoot i ν
local notation "W" => relativeWeylGroup i
local notation "roots" => rootSet i ν
local notation "p" => Standard.parabolicHom i ν
local notation "H" => height hi hK hρ
local notation "λ₀" => fundamentalWeight hG hi hν D
local notation "N₀" => AdelicSubgroupPoints.adelicPoints F G
  (SubgroupFunctor.range (Standard.unipotentHom i ν ∅))

set_option maxHeartbeats 1100000 in
theorem isTruncationIdempotent_of_unfolding_of_weylHeight
    (hunf : GeometricLemmaUnfoldingStatement.{u})
    (hHeight : ∀ (β : B) (a : normalizerPoints i), ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ (v : N₀) (y : A),
      pair T (λ₀ β) (H y) ≤ pair T (relativeWeylFullRealAction i (QuotientGroup.mk a) (λ₀ β))
        (H (innerAdelicPoint F G a.val * (v : A) * y)) + B₀) :
    IsTruncationIdempotent hG hi D hK hρ := by
  classical
  obtain ⟨hW, hB, M, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi ν hν
  let : Fintype B := Fintype.ofFinite _
  let : Fintype W := Fintype.ofFinite _
  let n (w : W) : normalizerPoints i := (QuotientGroup.mk_surjective w).choose
  have hn (w : W) : (QuotientGroup.mk (n w) : W) = w := (QuotientGroup.mk_surjective w).choose_spec
  have hwBound (β : B) (w : W) : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ (v : N₀) (y : A),
      pair T (λ₀ β) (H y) ≤ pair T (relativeWeylFullRealAction i w⁻¹ (λ₀ β))
        (H ((innerAdelicPoint F G (n w).val)⁻¹ * (v : A) * y)) + B₀ := by
    have hWInv : (QuotientGroup.mk (n w)⁻¹ : W) = w⁻¹ := by
      change (QuotientGroup.mk' _) ((n w)⁻¹) = _
      rw [map_inv, show (QuotientGroup.mk' _) (n w) = w from hn w]
    have hAInv : innerAdelicPoint F G ((n w)⁻¹).val = (innerAdelicPoint F G (n w).val)⁻¹ := by
      simp only [← principalPoint_eq_innerAdelicPoint, Subgroup.coe_inv, map_inv]
    simpa only [hWInv, hAInv] using hHeight β (n w)⁻¹
  obtain ⟨C, hC⟩ := exists_regular_weylPositivity hG hi hν D hK hρ n hn hwBound
  refine ⟨C, fun Tp hTp φ hφ => ?_⟩
  have hvanish (S : Finset (characterLattice T)) (hS : S ∈ (simpleFinset ν hG hi).powerset)
      (x : A) (hx : ∃ β ∈ simpleRelativeRoots i ν, β ∉ (S : Set (characterLattice T)) ∧
        0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β (H x - Tp)) :
      constantTerm F i ν (S : Set (characterLattice T)) (truncation hG hi D hK hρ Tp φ) x = 0 := by
    obtain ⟨Q, rfl⟩ := exists_labelFinset hG hi S hS
    obtain ⟨a, ha, hnot, hpos⟩ := hx
    rw [coe_labelFinset] at hnot ⊢
    let β : B := ⟨a, ha⟩
    have hβ : β ∉ Q := fun h => hnot ((val_mem_rootSet i ν Q β).mpr h)
    have htest : 0 < pair T (λ₀ β) (H x - Tp) := by
      rw [pair_fundamentalWeight hG hi hν D]
      exact hpos
    rw [constantTerm_truncation_eq_bruhat hG hi hν D hK hρ hunf cs hcs Q n hn Tp φ hφ x]
    simp_rw [Finset.mul_sum]
    rw [sum_minimal_swap cs Q]
    apply Finset.sum_eq_zero
    intro w hw
    refine bruhatCutoffSum_eq_zero_of_leftMinimal hG hi hν D hK hρ cs hcs hunf Q n hn w
      ((Finset.mem_filter.mp hw).2) β hβ Tp φ hφ x ?_
    intro delta v
    apply hC Tp hTp β w v ((delta : A) * x)
    have hdelta := pair_fundamentalWeight_parabolicRational_mul hG hi hν D hK hρ
      (rootSet_subset i ν Q) β hnot delta.2 x
    rwa [map_sub, hdelta, ← map_sub]
  refine ⟨hvanish, truncation_eq_self_of_constantTerm_vanishing hG hi hν D hK hρ Tp _ ?_ hvanish⟩
  exact fun r hr y => truncation_rational_mul hG hi hν D hK hρ Tp φ hφ.2.2 hr y

end Langlands.Global.ArthurTruncation.Idempotence
