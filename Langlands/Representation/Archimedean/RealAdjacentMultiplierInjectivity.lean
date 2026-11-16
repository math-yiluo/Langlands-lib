import Langlands.Representation.Archimedean.RealAmbientOrthogonalUncertainty
import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction

/-!
# Injectivity of block Fourier multipliers adjacent to an induction block

An ambient uncertainty argument makes a compact block multiplier injective when its zeros
are confined below a cutoff strictly smaller than the adjacent source induction weight.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealAdjacentMultiplier

open Langlands.LocalFactor.Archimedean RealBlockJacquet RealBlockFrobeniusMap
open scoped Matrix.Norms.Operator Manifold ContDiff

/-- A linear map on the compact-finite standard module with a prescribed block Fourier
multiplier on the compact group. The codomain consists of ambient functions. -/
structure CompactMultiplier (n : ℕ) (ds : List RealBlock) (q : ℕ) (μ : ℤ → ℂ) where
  toLinearMap : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
    (Langlands.GeneralLinear n ℝ → ℂ)
  fourier : ∀ f, ∀ k ∈ unitaryCompact ℝ n, ∀ j : ℤ,
    blockFourierCoefficient n q j (toLinearMap f) k =
      μ j * blockFourierCoefficient n q j f k

variable {n : ℕ} {ds es : List RealBlock} {p q : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

/-- The published Frobenius map as a compact multiplier with values in ambient functions. -/
def ofBlockFrobData (h : IsBlockFrobData n ds es q ε σ μ) :
    CompactMultiplier n ds q μ where
  toLinearMap := (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)).subtype.comp
    (blockFrobMap h)
  fourier f _k hk j := blockFourierCoefficient_blockFrobMap h f hk j

/-- A vector in the kernel is zero if it has high modes along the adjacent rotation and
the multiplier has no zeros on the source parity class beyond a strictly lower cutoff. -/
theorem eq_zero_of_map_eq_zero (p : ℕ) (hp : p + 3 ≤ n) {r s m m' : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hmm : m' < m)
    (T : CompactMultiplier n ds (p + s) μ)
    (hpar : (-1 : ℂ) ^ ε =
      realPositionCharacter ds (p + s) (-1) * realPositionCharacter ds (p + s + 1) (-1))
    (hμ : ∀ j : ℤ, Even (j - ε) → (m' : ℤ) ≤ |j| → μ j ≠ 0)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hhigh : ∀ k ∈ unitaryCompact ℝ n, ∀ j : ℤ, |j| < (m : ℤ) →
      blockFourierCoefficient n (p + r) j f k = 0)
    (hTf : T.toLinearMap f = 0) : f = 0 := by
  have hs : p + s + 1 < n := by
    rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hzero : ∀ k ∈ unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k = 0 := by
    apply RealOrthogonalBlock.adjacent_uncertainty p hp hrs hmm
      (contMDiff_of_mem_realStandardModule f.2.1).continuous f.2.2 hhigh
    intro k hk j hj
    by_cases hje : Even (j - ε)
    · have h := T.fourier f k hk j
      rw [hTf] at h
      have h0 : μ j * blockFourierCoefficient n (p + s) j f k = 0 := by
        simpa [blockFourierCoefficient] using h.symm
      exact (mul_eq_zero.mp h0).resolve_left (hμ j hje hj)
    · exact blockFourierCoefficient_eq_zero_of_not_even hs hpar f hje k
  apply Subtype.ext
  exact eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1 hzero

/-- A multiplier is injective if the source contains an adjacent induction block whose
absolute weight is strictly greater than a bound for its possible zeros. -/
theorem injective_of_induced (p : ℕ) (hp : p + 3 ≤ n) {r s m' : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0)
    (T : CompactMultiplier n ds (p + s) μ) {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds (p + r) = some d) (hcut : m' < d.weight.natAbs)
    (hpar : (-1 : ℂ) ^ ε =
      realPositionCharacter ds (p + s) (-1) * realPositionCharacter ds (p + s + 1) (-1))
    (hμ : ∀ j : ℤ, Even (j - ε) → (m' : ℤ) ≤ |j| → μ j ≠ 0) :
    Function.Injective T.toLinearMap := by
  have hker : ∀ f, T.toLinearMap f = 0 → f = 0 := by
    intro f hf
    apply eq_zero_of_map_eq_zero p hp hrs hcut T hpar hμ f ?_ hf
    intro k _ j hj
    exact f.2.1.2 (p + r) d hd j (by simpa using hj) k
  intro f g hfg
  exact sub_eq_zero.mp (hker (f - g) (by simp only [map_sub, hfg, sub_self]))

end Langlands.Archimedean.RealAdjacentMultiplier

namespace Langlands.Archimedean.RealBlockFrobeniusMap

open Langlands.LocalFactor.Archimedean RealBlockMultiplier

variable {n : ℕ} {ds es : List RealBlock} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

/-- The adjacent-window criterion applied to the published block Frobenius map. -/
theorem blockFrobMap_injective_of_adjacent_induced (p : ℕ) (hp : p + 3 ≤ n)
    {r s m' : ℕ} (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0)
    (h : IsBlockFrobData n ds es (p + s) ε σ μ) {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds (p + r) = some d) (hcut : m' < d.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - ε) → (m' : ℤ) ≤ |j| → μ j ≠ 0) :
    Function.Injective (blockFrobMap h) := by
  have hi := RealAdjacentMultiplier.injective_of_induced p hp hrs
    (RealAdjacentMultiplier.ofBlockFrobData h) hd hcut h.par hμ
  intro f g hfg
  apply hi
  exact congrArg Subtype.val hfg

/-- The published block Frobenius map satisfies the standard intertwiner clauses whenever
its multiplier satisfies the recurrence. -/
theorem isRealStandardIntertwiner_blockFrobMap {q : ℕ}
    (h : IsBlockFrobData n ds es q ε σ μ)
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds q -
      GramFormula.realPositionExponent ds (q + 1) + 1) ε μ) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds
      (blockFrobMap h) := by
  simpa using (isRealIntertwinerModulo_blockFrobMap h hrec ⊥).comp
    (isRealStandardIntertwiner_id n es) bot_le

/-- Recurrent Frobenius data with the adjacent-window criterion give an injective
standard intertwiner. No existence of such data is asserted. -/
theorem injectiveIntertwinerExists_of_adjacent_induced (p : ℕ) (hp : p + 3 ≤ n)
    {r s m' : ℕ} (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0)
    (h : IsBlockFrobData n ds es (p + s) ε σ μ) {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds (p + r) = some d) (hcut : m' < d.weight.natAbs)
    (hμ : ∀ j : ℤ, Even (j - ε) → (m' : ℤ) ≤ |j| → μ j ≠ 0)
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds (p + s) -
      GramFormula.realPositionExponent ds (p + s + 1) + 1) ε μ) :
    RealInjectiveIntertwinerExists n ds es :=
  ⟨blockFrobMap h, blockFrobMap_injective_of_adjacent_induced p hp hrs h hd hcut hμ,
    isRealStandardIntertwiner_blockFrobMap h hrec⟩

end Langlands.Archimedean.RealBlockFrobeniusMap
