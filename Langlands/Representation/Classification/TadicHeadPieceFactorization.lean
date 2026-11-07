import Langlands.Representation.Classification.TadicRectangleCombinatorics
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.TadicProductClosure
import Langlands.Representation.Classification.TadicXBlockAdapters
import Langlands.Representation.Classification.TadicExhaustionLemmasStatement
import Langlands.Representation.Classification.SpehUnitarizabilityStatement
import Langlands.Representation.Classification.LinkedSegmentOverlapInduction

/-!
# Products of Tadić blocks in Langlands form

`TadicSocleHeadDuality F T m` is Tadić's Theorem A.10(iii) up to rank `m`:
`⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` for unitary `ρ` and `n d deg ρ ≤ m`. Under it every
member of `X_m` is a product of Langlands heads of Tadić head pieces, and so is
every finite product of members of `X_m`. With Corollary A.6(ii) and the head
classification, a Langlands head of `a(d,n)^ρ` of rank `m+1` is therefore not
such a product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

variable (F T) in
/-- Tadić's Theorem A.10(iii) up to rank `m`: every Zelevinsky socle of `a(n,d)^ρ`
with `n, d > 0`, `ρ` unitary and rank at most `m` is a Langlands head of `a(d,n)^ρ`. -/
def TadicSocleHeadDuality (m : ℕ) : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hn : 0 < n) (hd : 0 < d), ρ.IsUnitary →
    ∀ {N : ℕ} (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      N ≤ m → (tadicMultisegment ρ n d hd).IsZelevinskySocle σ →
        (tadicMultisegment ρ d n hn).IsLanglandsHead σ

namespace TadicSocleHeadDuality

theorem mono {j k : ℕ} (hjk : j ≤ k) (h : TadicSocleHeadDuality.{uF, uV} F T k) :
    TadicSocleHeadDuality.{uF, uV} F T j := by
  let := T.topology
  intro ρ n d hn hd hρ N σ hN hσ
  exact h ρ n d hn hd hρ σ (hN.trans hjk) hσ

theorem zero : TadicSocleHeadDuality.{uF, uV} F T 0 := by
  let := T.topology
  intro ρ n d hn hd hρ N σ hN hσ
  have h := tadicMultisegment_rank_eq_of_isZelevinskySocle hσ
  have : 0 < n * (d * ρ.rank) := Nat.mul_pos hn (Nat.mul_pos hd ρ.rank_pos)
  omega

/-- Under A.10(iii) up to rank `m`, the rectangular socles are Speh representations. -/
theorem spehComparison {m : ℕ} (h : TadicSocleHeadDuality.{uF, uV} F T m) :
    TadicSocleSpehComparison.{uF, uV} F T m := by
  let := T.topology
  intro ρ n d hd hn hρ N σ hN hσ
  exact exists_isSpeh_of_isLanglandsHead hρ hn hd (h ρ n d hn hd hρ σ hN hσ)

/-- Under A.10(iii) up to rank `m` and Speh unitarizability, `(U^m)` holds. -/
theorem socleUnitarity {m : ℕ} (h : TadicSocleHeadDuality.{uF, uV} F T m)
    (hSU : SpehUnitarizability.{uF, uV} F T) : TadicSocleUnitarity.{uF, uV} F T m := by
  let := T.topology
  intro ρ n d hd hn hρ N σ hN hσ
  obtain ⟨D, S, hD, hS, ⟨e⟩⟩ := h.spehComparison ρ n d hd hn hρ σ hN hσ
  subst hD
  exact (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mp (hSU D hS.1 S hS)

end TadicSocleHeadDuality

variable (m : ℕ) in
/-- `π` is isomorphic to a normalized product of Langlands heads of Tadić head
pieces of degree bound `m`. -/
def HasTadicHeadPieceFactorization {N : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (B : BlockShape N)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, ∃ c : T.Multisegment.{max uF uV, uF}, IsTadicHeadPiece m c ∧ c.IsLanglandsHead (σ i)) ∧
      Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

private def headPieceReindexRankIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

private def headPieceFlattenedBlocks {n : ℕ} (B : BlockShape n)
    (S : ∀ i, BlockShape (B.size i))
    (τ : letI := T.topology
      ∀ i k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S i).size k) F.Carrier)) :
    letI := T.topology
    ∀ k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier) :=
  let e := B.flattenBlockEquiv S
  fun k => τ (e.symm k).1 (e.symm k).2

set_option maxHeartbeats 400000 in
private theorem headPieceFlattenedBlocks_inducedIso {n : ℕ} (B : BlockShape n)
    (S : ∀ i, BlockShape (B.size i))
    (τ : letI := T.topology
      ∀ i k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S i).size k) F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor (B.flatten S)).obj
      (headPieceFlattenedBlocks B S τ) ≅
        (T.normalizedProductInductionFunctor B).obj
          (fun i => (T.normalizedProductInductionFunctor (S i)).obj (τ i))) := by
  let := T.topology
  let e := B.flattenBlockEquiv S
  let C := B.flatten S
  let τflat := headPieceFlattenedBlocks B S τ
  have h (q : (j : Fin B.length) × Fin (S j).length) :
      (S q.1).size q.2 = C.size (e q) :=
    (B.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF,max uF uV}
    F T n C B S e h
    (fun j k x => B.index_index_eq_flatten S ⟨j,k⟩ x) τflat
  have einner (j : Fin B.length) :
      (T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j,k⟩).symm ▸ τflat (e ⟨j,k⟩)) ≅
      (T.normalizedProductInductionFunctor (S j)).obj (τ j) := by
    apply (T.normalizedProductInductionFunctor (S j)).mapIso
    apply Pi.isoMk
    intro k
    exact headPieceReindexRankIso
      (fun q : (j : Fin B.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => τ q.1 q.2) (e.symm_apply_apply ⟨j,k⟩)
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk einner)⟩

set_option maxHeartbeats 400000 in
/-- Products of head-piece products are head-piece products (induction in stages). -/
theorem hasTadicHeadPieceFactorization_normalizedProduct (m : ℕ) {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : ∀ i, HasTadicHeadPieceFactorization m (σ i)) :
    HasTadicHeadPieceFactorization m ((T.normalizedProductInductionFunctor B).obj σ) := by
  classical
  let := T.topology
  change ∀ i, ∃ (S : BlockShape (B.size i))
    (τ : ∀ k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (S.size k) F.Carrier)),
    (∀ k, ∃ c : T.Multisegment.{max uF uV, uF}, IsTadicHeadPiece m c ∧
      c.IsLanglandsHead (τ k)) ∧
      Nonempty (σ i ≅ (T.normalizedProductInductionFunctor S).obj τ) at hσ
  choose S τ hτ hστ using hσ
  let eστ := fun i => Classical.choice (hστ i)
  obtain ⟨eflat⟩ := headPieceFlattenedBlocks_inducedIso B S τ
  let e := B.flattenBlockEquiv S
  refine ⟨B.flatten S, headPieceFlattenedBlocks B S τ,
    fun k => hτ (e.symm k).1 (e.symm k).2, ?_⟩
  exact ⟨(T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk eστ) ≪≫ eflat.symm⟩

/-- A one-block normalized product is its factor. -/
def oneBlockProductIso {N : ℕ} (hN : 0 < N)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (CuspidalSupport.LeviAdmissibility.oneBlock N hN)).obj
      (fun _ => π) ≅ π :=
  letI := T.topology
  SmoothRep.mkIso (QuotientHom.oneBlockInducedEquiv N hN π)

/-- A Langlands head of a head piece is a one-block head-piece product. -/
theorem hasTadicHeadPieceFactorization_of_isLanglandsHead {m N : ℕ} (hN : 0 < N)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    {c : T.Multisegment.{max uF uV, uF}} (hc : IsTadicHeadPiece m c)
    (h : c.IsLanglandsHead π) : HasTadicHeadPieceFactorization m π :=
  letI := T.topology
  ⟨CuspidalSupport.LeviAdmissibility.oneBlock N hN, fun _ => π, fun _ => ⟨c, hc, h⟩,
    ⟨(oneBlockProductIso hN π).symm⟩⟩

/-- Under A.10(iii) up to rank `m`, every member of `X_m` is a head-piece product. -/
theorem TadicSocleHeadDuality.hasTadicHeadPieceFactorization {m N : ℕ}
    (h : TadicSocleHeadDuality.{uF, uV} F T m)
    {τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hτ : IsTadicXBlock m τ) : HasTadicHeadPieceFactorization m τ := by
  let := T.topology
  rcases hτ with ⟨ρ, n, d, hd, hn, hρ, hNk, hσ⟩ |
    ⟨ρ, n, d, hd, M, hM, σ, α, hMN, hn, hρ, hMk, hσ, hα0, hα, ⟨eτ⟩⟩
  · have hhead := h ρ n d hn hd hρ τ hNk hσ
    have hN := tadicMultisegment_rank_eq_of_isZelevinskySocle hσ
    have hpos : 0 < N := by
      rw [hN]
      exact Nat.mul_pos hn (Nat.mul_pos hd ρ.rank_pos)
    refine hasTadicHeadPieceFactorization_of_isLanglandsHead hpos
      ⟨ρ, d, n, hn, hd, hρ, Or.inl ⟨rfl, ?_⟩⟩ hhead
    rw [tadicMultisegment_degree]
    have : d * (n * ρ.rank) = n * (d * ρ.rank) := by ring
    omega
  · subst hMN
    have hhead := h ρ n d hn hd hρ σ hMk hσ
    refine ⟨BlockShape.uniform 2 M hM,
      fun i => T.segmentFactor σ (if (i : ℕ) = 0 then α else -α), fun i => ?_, ⟨eτ.symm⟩⟩
    refine ⟨(tadicMultisegment ρ d n hn).twist (if (i : ℕ) = 0 then α else -α),
      ⟨ρ, d, n, hn, hd, hρ, Or.inr ⟨_, ?_, ?_, rfl⟩⟩, ?_⟩
    · split_ifs <;> simp only [abs_neg, abs_of_pos hα0] <;> linarith
    · split_ifs <;> simp only [abs_neg, abs_of_pos hα0] <;> linarith
    · exact ((multisegmentConstituentRealTwistCompatibility.{uF, max uF uV} F T M hM _
        (if (i : ℕ) = 0 then α else -α) σ).2).mp hhead

/-- The core of Tadić's A.10 step: under A.10(iii) up to rank `m`, Corollary A.6(ii)
and the head classification, a Langlands head of `a(d,n)^ρ` of rank `m+1` is not a
product of members of `X_m`. -/
theorem TadicSocleHeadDuality.not_iso_xBlockProduct {m : ℕ}
    (h : TadicSocleHeadDuality.{uF, uV} F T m)
    (hP10 : IrreducibleLanglandsHeadProduct.{uF, uV} F T)
    (hHC : MultisegmentHeadClassification.{uF, uV} F T)
    {ρ : T.CuspidalDatum.{max uF uV, uF}} (hρ : ρ.IsUnitary) {n d : ℕ} (hn : 0 < n)
    (hd : 0 < d)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier)}
    (hπ : (tadicMultisegment ρ d n hn).IsLanglandsHead π) (B : BlockShape (m + 1))
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : ∀ i, IsTadicXBlock m (σ i))
    (e : letI := T.topology; π ≅ (T.normalizedProductInductionFunctor B).obj σ) : False := by
  let := T.topology
  obtain ⟨B', π', hπ', ⟨e'⟩⟩ := hasTadicHeadPieceFactorization_normalizedProduct m B σ
    (fun i => h.hasTadicHeadPieceFactorization (hσ i))
  choose c hc hch using hπ'
  have hπi : π.IsIrreducible := by
    obtain ⟨E, -, -, -, hi, -⟩ := hπ
    exact hi
  have hirr : Representation.IsIrreducible
      ((T.normalizedProductInductionFunctor B').obj π').representation :=
    (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso (e ≪≫ e'))).mp hπi
  have hhead := hP10 (m + 1) B' c π' hch hirr
  have heq := (hHC (m + 1) _ _ π _ hπ hhead).mpr ⟨e ≪≫ e'⟩
  have hdeg : m < (tadicMultisegment ρ d n hn).degree := by
    rw [tadicMultisegment_degree, ← tadicMultisegment_rank_eq_of_isLanglandsHead hπ]
    omega
  exact not_sum_tadicHeadPieces hρ hn hd hdeg c hc heq.symm

end Langlands.Classification
