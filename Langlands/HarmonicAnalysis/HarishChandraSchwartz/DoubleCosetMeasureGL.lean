import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure
import Langlands.Group.GL.CartanCellCountProof

/-! # The upper bound of Waldspurger I.1 (5) for `GL_n`

For `G = GL_n(F)` over a `p`-adic field, `K = GL_n(O)` and the diagonal representative
`a(λ)` of an antitone exponent tuple `λ`, the Library's `cartanCellCount` (Worker 23) covers
`K a(λ) K` by at most `c δ(λ)⁻¹` left translates `r a(λ) K`, where `δ(λ) = q^{-deg λ}` is the
modulus of the upper Borel subgroup at `a(λ)`. This module deduces the bound
`[K : K ∩ a(λ) K a(λ)⁻¹] ≤ c δ(λ)⁻¹` (`GLDoubleCosetIndexBound`) for the index
`doubleCosetIndex` of `DoubleCosetMeasure`,
and hence `μ(K a(λ) K) ≤ c δ(λ)⁻¹ μ(K)` for every left invariant measure `μ`: the upper bound
of Waldspurger's I.1 (5) for `GL_n`.
-/

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory
open Langlands.GeneralLinear.CartanQuotient

namespace Langlands.HarishChandraSchwartz

universe uF

section Cover

variable {G : Type*} [Group G]

/-- If every `k₁ g k₂` with `k₁, k₂ ∈ K` lies in `r g K` for some `r` in a finite set `R`, then
`[K : K ∩ g K g⁻¹]` is finite and at most the cardinality of `R`. -/
theorem doubleCosetIndex_le_of_cover {K : Subgroup G} {g : G} {R : Finset G}
    (hR : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∃ r ∈ R, ∃ k ∈ K, k₁ * g * k₂ = r * g * k) :
    doubleCosetIndex K g ≠ 0 ∧ doubleCosetIndex K g ≤ R.card := by
  classical
  set L := (conjSubgroup g K).subgroupOf K
  have hchoice : ∀ q : K ⧸ L, ∃ r ∈ R, ∃ k ∈ K, ((q.out : K) : G) * g * 1 = r * g * k :=
    fun q => hR _ (q.out : K).2 1 K.one_mem
  choose r hrR k hkK hrk using hchoice
  let φ : K ⧸ L → R := fun q => ⟨r q, hrR q⟩
  have hcoset : ∀ q : K ⧸ L,
      (((q.out : K) : G) * g) • (K : Set G) = (r q * g) • (K : Set G) := by
    intro q
    rw [leftCoset_eq_iff (s := K)]
    have h := hrk q
    rw [mul_one] at h
    rw [h]
    simpa [mul_assoc] using K.inv_mem (hkK q)
  have hinj : Function.Injective φ := by
    intro q q' hqq'
    have hr : r q = r q' := congrArg Subtype.val hqq'
    have h := (hcoset q).trans ((congrArg (fun x => (x * g) • (K : Set G)) hr).trans
      (hcoset q').symm)
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (translate_smul_eq_iff K g _ _).mp h
  have hfin : Finite (K ⧸ L) := Finite.of_injective φ hinj
  have hcard : Nat.card (K ⧸ L) ≤ R.card := by
    have := Nat.card_le_card_of_injective φ hinj
    simpa using this
  refine ⟨?_, ?_⟩
  · change Nat.card (K ⧸ L) ≠ 0
    exact Nat.card_pos.ne'
  · exact hcard

end Cover

section GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) (n : ℕ)

/-- The index form of the upper bound of I.1 (5) for `GL_n`: one constant `c` such that, for
every antitone `λ`, `[K : K ∩ a(λ) K a(λ)⁻¹]` is finite and at most `c δ(λ)⁻¹`, where
`K = GL_n(O)`, `a(λ)` is the diagonal representative and `δ(λ) = q^{-deg λ}`. -/
def GLDoubleCosetIndexBound : Prop :=
  ∃ c : ℝ, ∀ lam : Fin n → ℤ, Antitone lam →
    doubleCosetIndex (maximalCompact T n) (representative T lam) ≠ 0 ∧
      (doubleCosetIndex (maximalCompact T n) (representative T lam) : ℝ) ≤
        c * (delta T lam)⁻¹

/-- `GLDoubleCosetIndexBound` holds, by the Library's `cartanCellCount`. -/
theorem glDoubleCosetIndexBound : GLDoubleCosetIndexBound T n := by
  obtain ⟨c, hc⟩ := cartanCellCount p F T n
  refine ⟨c, fun lam hlam => ?_⟩
  obtain ⟨R, hRcard, hR⟩ := hc lam hlam
  obtain ⟨h0, hle⟩ := doubleCosetIndex_le_of_cover hR
  exact ⟨h0, (Nat.cast_le.mpr hle).trans hRcard⟩

/-- The upper bound of Waldspurger I.1 (5) for `GL_n`: for every left invariant measure `μ` on
`GL_n(F)` (for any measurable structure with measurable multiplication in which `K` is
measurable), `μ(K a(λ) K) ≤ c δ(λ)⁻¹ μ(K)` for all antitone `λ`. -/
theorem exists_measure_doubleCoset_le_delta
    [MeasurableSpace (GeneralLinear n F.Carrier)] [MeasurableMul (GeneralLinear n F.Carrier)]
    (μ : Measure (GeneralLinear n F.Carrier)) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (maximalCompact T n : Set (GeneralLinear n F.Carrier))) :
    ∃ c : ℝ, ∀ lam : Fin n → ℤ, Antitone lam →
      μ (DoubleCoset.doubleCoset (representative T lam) (maximalCompact T n)
          (maximalCompact T n)) ≤
        ENNReal.ofReal (c * (delta T lam)⁻¹) * μ (maximalCompact T n) := by
  obtain ⟨c, hc⟩ := glDoubleCosetIndexBound T n
  refine ⟨c, fun lam hlam => ?_⟩
  obtain ⟨h0, hle⟩ := hc lam hlam
  rw [measure_doubleCoset μ _ hK _ h0]
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hle

end GeneralLinearGroup

end Langlands.HarishChandraSchwartz
