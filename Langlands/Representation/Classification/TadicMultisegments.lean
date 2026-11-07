import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport

/-!
# Tadić's multisegments `a(n,d)^ρ` and the block set `X_k`

Tadić 1986, §3.1: `Δ[d]^ρ = [ν^(-(d-1)/2) ρ, ν^((d-1)/2) ρ]`, and
`a(n,d)^ρ` is the multisegment of the `n` twists `ν^(-(n-1)/2 + j) Δ[d]^ρ`,
`0 ≤ j < n`. Tadić's §4.6 set `X_(m-1)` of Lemma 4.8 consists of the Zelevinsky
representations `⟨a(n,d)^ρ⟩` with `n, d > 0`, `ρ` unitary and `n d deg ρ ≤ m-1`, and
of the complementary products `ν^α σ × ν^(-α) σ` of such `σ` with `0 < α < 1/2`.
Everything here is a definition or relation; no existence is asserted.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The segment `ν^x Δ[d]^ρ = [ν^(x-(d-1)/2) ρ, ν^(x+(d-1)/2) ρ]` of length `d`
centered at the real exponent `x`. -/
def tadicCenteredSegment (ρ : T.CuspidalDatum.{uV, uF}) (d : ℕ) (hd : 0 < d) (x : ℝ) :
    T.Segment.{uV, uF} where
  base := ρ.twist (x - ((d : ℝ) - 1) / 2)
  length := d
  length_pos := hd

@[simp]
theorem tadicCenteredSegment_length (ρ : T.CuspidalDatum.{uV, uF}) (d : ℕ) (hd : 0 < d)
    (x : ℝ) : (tadicCenteredSegment ρ d hd x).length = d := rfl

@[simp]
theorem tadicCenteredSegment_rank (ρ : T.CuspidalDatum.{uV, uF}) (d : ℕ) (hd : 0 < d)
    (x : ℝ) : (tadicCenteredSegment ρ d hd x).rank = ρ.rank := rfl

/-- Tadić's `a(n,d)^ρ`: the `n` segments `ν^(j-(n-1)/2) Δ[d]^ρ`, `0 ≤ j < n`.
Thus `a(1,d)^ρ = Δ[d]^ρ` and `a(n,1)^ρ` consists of `n` one-point segments. Tadić
takes `n > 0`; the raw construction also allows `n = 0`, giving the empty
multisegment, which the predicates below exclude. -/
def tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hd : 0 < d) :
    T.Multisegment.{uV, uF} :=
  (Multiset.range n).map fun j : ℕ => tadicCenteredSegment ρ d hd ((j : ℝ) - ((n : ℝ) - 1) / 2)

/-- `a(n,d)^ρ` has `n` segments. -/
@[simp]
theorem tadicMultisegment_card (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hd : 0 < d) :
    Multiset.card (tadicMultisegment ρ n d hd) = n := by
  simp [tadicMultisegment]

/-- `a(n,d)^ρ` lives on `GL_(n d deg ρ)`. -/
theorem tadicMultisegment_degree (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hd : 0 < d) :
    (tadicMultisegment ρ n d hd).degree = n * (d * ρ.rank) := by
  unfold tadicMultisegment PadicField.TopologicalData.Multisegment.degree
  rw [Multiset.map_map]
  have h : (PadicField.TopologicalData.Segment.degree ∘ fun j : ℕ =>
      tadicCenteredSegment ρ d hd ((j : ℝ) - ((n : ℝ) - 1) / 2)) = fun _ => d * ρ.rank := by
    funext j
    rfl
  rw [h, Multiset.map_const', Multiset.card_range, Multiset.sum_replicate, smul_eq_mul]

/-- The actual binary normalized product `ν^α σ × ν^(-α) σ` of the two opposite real
twists of the same representation `σ` of `GL_M`. Tadić's `π(σ, α)` is
`ν^α σ × ν^(-α) σ^+` with the Hermitian contragredient `σ^+`; the two agree when `σ`
is Hermitian. For `M = d.degree` this is `SpehDatum.complementaryInduced` by
definition. -/
def tadicComplementaryProduct {M : ℕ} (hM : 0 < M)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier))
    (α : ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * M) F.Carrier) :=
  T.twistedProductInduced (BlockShape.uniform 2 M hM) (fun _ => σ)
    (fun i => if (i : ℕ) = 0 then α else -α)

theorem SpehDatum.complementaryInduced_eq_tadicComplementaryProduct
    (d : SpehDatum.{uF, uV} F T)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)) (α : ℝ) :
    d.complementaryInduced S α =
      tadicComplementaryProduct (Nat.mul_pos d.length_pos d.rank_pos) S α :=
  rfl

/-- Membership in Tadić's set `X_k` (Lemma 4.8 uses `k = m-1`), for a representation
`τ` of `GL_N`: either `τ` is a Zelevinsky socle `⟨a(n,d)^ρ⟩` with `n, d > 0`, `ρ`
unitary and `N ≤ k`, or `τ` is isomorphic to `ν^α σ × ν^(-α) σ` for such a socle `σ`
of `GL_M`, `M ≤ k`, `N = 2 M` and `0 < α < 1/2`. -/
def IsTadicXBlock (k : ℕ) {N : ℕ}
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)) : Prop :=
  letI := T.topology
  (∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d),
      0 < n ∧ ρ.IsUnitary ∧ N ≤ k ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle τ) ∨
    (∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d) (M : ℕ) (hM : 0 < M)
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)) (α : ℝ)
      (h : 2 * M = N),
      0 < n ∧ ρ.IsUnitary ∧ M ≤ k ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle σ ∧
        0 < α ∧ α < (1 / 2 : ℝ) ∧ Nonempty ((h ▸ tadicComplementaryProduct hM σ α) ≅ τ))

/-- A Zelevinsky socle of `a(n,d)^ρ` on `GL_N` has `N = n d deg ρ`. -/
theorem tadicMultisegment_rank_eq_of_isZelevinskySocle {ρ : T.CuspidalDatum.{max uF uV, uF}}
    {n d : ℕ} {hd : 0 < d} {N : ℕ}
    {σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : (tadicMultisegment ρ n d hd).IsZelevinskySocle σ) : N = n * (d * ρ.rank) := by
  obtain ⟨D, hD, -⟩ := h
  have hdeg : D.multisegment.degree = N := by
    simpa [PadicField.TopologicalData.Multisegment.degree,
      PadicField.TopologicalData.SegmentProductDatum.multisegment, List.map_ofFn,
      List.sum_ofFn] using D.degree_sum
  rw [hD, tadicMultisegment_degree] at hdeg
  exact hdeg.symm

/-- Every member of `X_k` lives on `GL_N` with `N > 0`. -/
theorem IsTadicXBlock.rank_pos {k N : ℕ}
    {τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : IsTadicXBlock k τ) : 0 < N := by
  rcases h with ⟨ρ, n, d, hd, hn, -, -, hs⟩ | ⟨ρ, n, d, hd, M, hM, σ, α, hMN, -, -, -, -, -, -, -⟩
  · rw [tadicMultisegment_rank_eq_of_isZelevinskySocle hs]
    exact Nat.mul_pos hn (Nat.mul_pos hd ρ.rank_pos)
  · omega

/-- Tadić's `X_0` is empty. -/
theorem not_isTadicXBlock_zero {N : ℕ}
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)) :
    ¬ IsTadicXBlock 0 τ := by
  intro h
  have hN := h.rank_pos
  rcases h with ⟨-, -, -, -, -, -, hNk, -⟩ | ⟨-, -, -, -, M, hM, -, -, -, -, -, hMk, -⟩
  · omega
  · omega

variable (F T) in
/-- Tadić's statement `(U^m)` (1986, §4.6): for every unitary cuspidal `ρ` and all
`n, d > 0` with `n d deg ρ ≤ m`, the representation `⟨a(n,d)^ρ⟩` is unitarizable. It is
stated for every Zelevinsky socle `σ` of `a(n,d)^ρ` on `GL_N` with `N ≤ m`; such a
socle lives on `GL_(n d deg ρ)`. -/
def TadicSocleUnitarity (m : ℕ) : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d), 0 < n → ρ.IsUnitary →
    ∀ {N : ℕ} (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      N ≤ m → (tadicMultisegment ρ n d hd).IsZelevinskySocle σ →
        IsUnitarizable σ.representation

end Langlands.Classification
