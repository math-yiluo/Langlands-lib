import Langlands.Representation.Classification.TadicHeadPieceFactorization

/-!
# Tadić's Theorem A.10: the exhaustion from its ingredients

Tadić's induction on the rank (1986, proof of Theorem A.10, printed pp.378-379)
proves `⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` for unitary `ρ` in every rank, and with it the
exhaustion of the unitary dual by products of Speh representations and
complementary series. The inputs are Lemma 4.8(ii), Lemma 6.3, Corollary A.6(ii),
Theorem A.8 (Speh unitarizability) and the classification of Langlands heads by
multisegments.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A representation isomorphic, after rank transport, to a Speh representation is
unitarizable, given Theorem A.8. -/
theorem isUnitarizable_of_isSpeh (hSU : SpehUnitarizability.{uF, uV} F T) {N : ℕ}
    {D : SpehDatum.{uF, uV} F T}
    {S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear D.degree F.Carrier)}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hD : D.degree = N) (hS : D.IsSpeh S) (e : letI := T.topology; (hD ▸ S) ≅ π) :
    letI := T.topology; IsUnitarizable π.representation := by
  let := T.topology
  subst hD
  exact (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mp (hSU D hS.1 S hS)

/-- Tadić's step "`L(a(n,d)^ρ)` is some `⟨a(u,v)^σ⟩`, hence `⟨a(n,d)^ρ⟩` or
`⟨a(d,n)^ρ⟩`": under A.10(iii) up to rank `m`, a Langlands head of `a(d,n)^ρ` on
`GL_(m+1)` is a Zelevinsky socle of `a(n,d)^ρ` or of `a(d,n)^ρ`. -/
theorem TadicSocleHeadDuality.isZelevinskySocle_of_isLanglandsHead {m : ℕ}
    (h : TadicSocleHeadDuality.{uF, uV} F T m)
    (hP8 : TadicBlockReduction.{uF, uV} F T)
    (hP10 : IrreducibleLanglandsHeadProduct.{uF, uV} F T)
    (hSU : SpehUnitarizability.{uF, uV} F T)
    (hHC : MultisegmentHeadClassification.{uF, uV} F T)
    {ρ : T.CuspidalDatum.{max uF uV, uF}} (hρ : ρ.IsUnitary) {n d : ℕ} (hn : 0 < n)
    (hd : 0 < d)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier)}
    (hπ : (tadicMultisegment ρ d n hn).IsLanglandsHead π) :
    (tadicMultisegment ρ n d hd).IsZelevinskySocle π ∨
      (tadicMultisegment ρ d n hn).IsZelevinskySocle π := by
  let := T.topology
  have hπi : π.IsIrreducible := by
    obtain ⟨E, -, -, -, hi, -⟩ := hπ
    exact hi
  have hπu : IsUnitarizable π.representation := by
    obtain ⟨D, S, hD, hS, ⟨e⟩⟩ := exists_isSpeh_of_isLanglandsHead hρ hn hd hπ
    exact isUnitarizable_of_isSpeh hSU hD hS e
  by_cases hex : ∃ (τ : T.CuspidalDatum.{max uF uV, uF}) (u v : ℕ) (hv : 0 < v),
      0 < u ∧ τ.IsUnitary ∧ (tadicMultisegment τ u v hv).IsZelevinskySocle π
  · obtain ⟨τ, u, v, hv, hu, hτ, hs⟩ := hex
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
      tadic_parameters_of_isZelevinskySocle_of_isLanglandsHead hρ hτ hu hv hd hn hs hπ
    · exact Or.inr hs
    · exact Or.inl hs
  · obtain ⟨B, σ, hσ, ⟨e⟩⟩ := hP8 m (h.socleUnitarity hSU) π hπi hπu hex
    exact (h.not_iso_xBlockProduct hP10 hHC hρ hn hd hπ B σ hσ e).elim

/-- The induction step of Tadić's Theorem A.10(iii). -/
theorem TadicSocleHeadDuality.succ {m : ℕ} (h : TadicSocleHeadDuality.{uF, uV} F T m)
    (hP8 : TadicBlockReduction.{uF, uV} F T)
    (hP9 : TadicRectangleHeadSocleDistinct.{uF, uV} F T)
    (hP10 : IrreducibleLanglandsHeadProduct.{uF, uV} F T)
    (hSU : SpehUnitarizability.{uF, uV} F T)
    (hHC : MultisegmentHeadClassification.{uF, uV} F T) :
    TadicSocleHeadDuality.{uF, uV} F T (m + 1) := by
  let := T.topology
  intro ρ n d hn hd hρ N σ hN hσ
  rcases Nat.lt_or_ge N (m + 1) with hlt | hge
  · exact h ρ n d hn hd hρ σ (by omega) hσ
  obtain rfl : N = m + 1 := le_antisymm hN hge
  have hrank := tadicMultisegment_rank_eq_of_isZelevinskySocle hσ
  have hdeg₁ : (tadicMultisegment ρ d n hn).degree = m + 1 := by
    rw [tadicMultisegment_degree, hrank]
    ring
  have hdeg₂ : (tadicMultisegment ρ n d hd).degree = m + 1 := by
    rw [tadicMultisegment_degree, hrank]
  obtain ⟨π, hπ⟩ := exists_isLanglandsHead_tadicMultisegment hρ hn hd hdeg₁
  have hQ := h.isZelevinskySocle_of_isLanglandsHead hP8 hP10 hSU hHC hρ hn hd hπ
  -- If `π` is a socle of `a(n,d)^ρ`, it is isomorphic to `σ`.
  have hdone : (tadicMultisegment ρ n d hd).IsZelevinskySocle π →
      (tadicMultisegment ρ d n hn).IsLanglandsHead σ := fun hs => by
    obtain ⟨e⟩ := nonempty_iso_of_isZelevinskySocle hs hσ
    exact Multisegment.IsLanglandsHead.of_iso hπ e
  rcases hQ with hs | hs
  · exact hdone hs
  rcases lt_trichotomy n d with hnd | rfl | hdn
  · -- `n < d`: compare with a Langlands head of `a(n,d)^ρ`.
    obtain ⟨π', hπ'⟩ := exists_isLanglandsHead_tadicMultisegment hρ hd hn hdeg₂
    rcases h.isZelevinskySocle_of_isLanglandsHead hP8 hP10 hSU hHC hρ hd hn hπ' with
      hs' | hs'
    · obtain ⟨e⟩ := nonempty_iso_of_isZelevinskySocle hs hs'
      have heq := (hHC (m + 1) _ _ π π' hπ hπ').mpr ⟨e⟩
      have hcard := congrArg Multiset.card heq
      rw [tadicMultisegment_card, tadicMultisegment_card] at hcard
      omega
    · exact (hP9 ρ n d hd hn hnd π' π' hπ' hs' ⟨Iso.refl _⟩).elim
  · exact hdone hs
  · -- `d < n`: Lemma 6.3 for `a(d,n)^ρ`.
    exact (hP9 ρ d n hn hd hdn π π hπ hs ⟨Iso.refl _⟩).elim

/-- Tadić's Theorem A.10(iii) in every rank. -/
theorem tadicSocleHeadDuality (hP8 : TadicBlockReduction.{uF, uV} F T)
    (hP9 : TadicRectangleHeadSocleDistinct.{uF, uV} F T)
    (hP10 : IrreducibleLanglandsHeadProduct.{uF, uV} F T)
    (hSU : SpehUnitarizability.{uF, uV} F T)
    (hHC : MultisegmentHeadClassification.{uF, uV} F T) (m : ℕ) :
    TadicSocleHeadDuality.{uF, uV} F T m := by
  induction m with
  | zero => exact TadicSocleHeadDuality.zero
  | succ m ih => exact ih.succ hP8 hP9 hP10 hSU hHC

/-- Tadić's exhaustion (Theorem A.10(ii), i.e. Theorem D(ii)) from Lemma 4.8(ii),
Lemma 6.3, Corollary A.6(ii), Theorem A.8 and the classification of Langlands
heads. -/
theorem tadicUnitaryDualExhaustion_of_ingredients
    (hP : TadicExhaustionLemmaStatements.{uF, uV} F T)
    (hSU : SpehUnitarizability.{uF, uV} F T)
    (hHC : MultisegmentHeadClassification.{uF, uV} F T) :
    TadicUnitaryDualExhaustion.{uF, uV} F T := by
  let := T.topology
  obtain ⟨hP8, hP9, hP10⟩ := hP
  have hR := tadicSocleHeadDuality hP8 hP9 hP10 hSU hHC
  intro n π hπi hπu
  by_cases hex : ∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (u v : ℕ) (hv : 0 < v),
      0 < u ∧ ρ.IsUnitary ∧ (tadicMultisegment ρ u v hv).IsZelevinskySocle π
  · obtain ⟨ρ, u, v, hv, hu, hρ, hs⟩ := hex
    have hb : IsTadicBuildingBlock F T π :=
      isTadicBuildingBlock_of_isTadicXBlock (hR (n + 1)).spehComparison
        (Or.inl ⟨ρ, u, v, hv, hu, hρ, le_rfl, hs⟩)
    exact ⟨CuspidalSupport.LeviAdmissibility.oneBlock (n + 1) n.succ_pos, fun _ => π,
      fun _ => hb, ⟨(oneBlockProductIso n.succ_pos π).symm⟩⟩
  · obtain ⟨B, σ, hσ, e⟩ := hP8 n ((hR n).socleUnitarity hSU) π hπi hπu hex
    exact ⟨B, σ, fun i => isTadicBuildingBlock_of_isTadicXBlock (hR n).spehComparison (hσ i),
      e⟩

end Langlands.Classification
