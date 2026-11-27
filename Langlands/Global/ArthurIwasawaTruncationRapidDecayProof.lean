import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.ArthurSiegelReductionProof
import Langlands.Global.ArthurSigmaSummandBounds
import Langlands.Global.ArthurSiegelCosetSum
import Langlands.Global.AdelicRationalHeightSummability

/-! # Arthur's restricted rapid decay for every compact Iwasawa subgroup -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints ArthurParabolicSpaces AdelicSiegelFactors RepresentationGrowth

/-- Arthur 2005, Proposition 13.2(a), for the restricted full-adelic input
space and every compact subgroup admitting the Iwasawa decomposition. -/
theorem iwasawaTruncationRapidDecay : IwasawaTruncationRapidDecayStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ N d ρ hSmooth hN hClosed
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C₀, T₀, hC₀, hcover⟩ := iwasawaSiegelCovering F G T i ν hG hi hν K hK hρ
  have hred := iwasawaSiegelReduction F G T i ν hG hi hν K hK hρ
  obtain ⟨c, hRegroup⟩ := arthurTruncationSigmaExpansion hG hi hν D hK hρ C₀ T₀ hC₀ hcover hred
  refine ⟨c, fun Tp hTp f hf C _ T₁ n => ?_⟩
  let A := AdelicGroupPoints F G
  let Γ := rationalSubgroup F G
  let X := siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁
  let Δ := simpleFinset ν hG hi
  let J := Finset (characterLattice T)
  let PQuot (R : J) := ParabolicRationalCosets F (Standard.parabolicHom i ν (R : Set (characterLattice T)))
  let φ := evaluate F G f.val
  let g := truncation hG hi D hK hρ Tp φ
  let H := adelicHeight F G ρ
  let Hs := adelicSourceNorm F G ρ
  let W := siegelSigmaCoefficient hG hi D hK hρ C₀ T₀ Tp
  let term (R S : J) (x : A) (j : PQuot R) :=
    let y := ((Quotient.out j : Γ) : A) * x
    (W R S y : ℂ) * alternatingConstantTerm (ν := ν) hG hi R S φ y
  let total (R S : J) (x : A) := ∑' j : PQuot R, term R S x j
  have hExpansion (x : A) : g x = ∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), total R S x := by
    exact (hRegroup Tp hTp f.val x).2
  obtain ⟨Cmin, hCmin, hmin⟩ := arthurSiegelNormMinimality F G T i ν hG hi hν K hK hρ ρ hN C T₁
  obtain ⟨a, ha⟩ := rationalAdelicHeightSummability F G ρ hN hClosed
  obtain ⟨m, Csum, hCsum, hsum⟩ := siegelCosetSumDecay.{u, u} F G ρ hN a ha Cmin hCmin n
  have hPair (R S : J) : ∃ B : ℝ, 0 ≤ B ∧ (R ⊆ S → S ⊆ Δ →
      ∀ x ∈ X, x ∈ normOneSubgroup F G → ‖total R S x‖ * H x ^ n ≤ B) := by
    by_cases h : R ⊆ S ∧ S ⊆ Δ
    · obtain ⟨B, hB, hrep⟩ := exists_sigmaCoset_representatives_with_bound hG hi hν D hK hρ C₀ T₀ Tp
        ρ hN hSmooth hC₀ R S h.1 h.2 f hf m
      refine ⟨Csum * B, mul_nonneg hCsum hB, fun _ _ x hx hxN => ?_⟩
      obtain ⟨e, he⟩ := hrep x hxN
      exact (hsum x (PQuot R) e (term R S x) B hB (fun j => hmin x hx (e j)) he).2
    · exact ⟨0, le_rfl, fun hRS hS => (h ⟨hRS, hS⟩).elim⟩
  choose B hB hBound using hPair
  let Cfinal := ∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), B R S
  refine ⟨Cfinal, fun x hx hxN => ?_⟩
  have hNorm : ‖g x‖ ≤ ∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), ‖total R S x‖ := by
    rw [hExpansion]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun R _ => norm_sum_le _ _)
  have hxH : 0 ≤ H x := le_trans zero_le_one (one_le_adelicHeight F G ρ hN x)
  have hWeighted : ‖g x‖ * H x ^ n ≤ Cfinal := by
    calc
      _ ≤ (∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), ‖total R S x‖) * H x ^ n :=
        mul_le_mul_of_nonneg_right hNorm (pow_nonneg hxH _)
      _ = ∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), ‖total R S x‖ * H x ^ n := by
        simp only [Finset.sum_mul]
      _ ≤ Cfinal := by
        refine Finset.sum_le_sum fun R _ => Finset.sum_le_sum fun S hS => ?_
        obtain ⟨hSΔ, hRS⟩ := Finset.mem_filter.mp hS
        exact hBound R S hRS (Finset.mem_powerset.mp hSΔ) x hx hxN
  have hxHs : 0 < Hs x := adelicSourceNorm_pos F G ρ hN x
  have hxCompare : Hs x ≤ H x := by
    rw [show H x = (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * Hs x from
      adelicHeight_eq_scalar_mul_sourceNorm F G ρ x]
    exact le_mul_of_one_le_left hxHs.le (one_le_pow₀ (by exact_mod_cast hN))
  have hFinal := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxHs.le hxCompare n)
    (norm_nonneg (g x))).trans hWeighted
  change ‖g x‖ ≤ Cfinal * Hs x ^ (-(n : ℝ))
  rw [Real.rpow_neg hxHs.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hxHs n)).mpr hFinal

end Langlands.Global.ArthurTruncation
