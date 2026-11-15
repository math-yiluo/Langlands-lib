import Langlands.Representation.Classification.MoeglinWaldspurgerHeadMoves
import Langlands.Representation.Classification.MoeglinWaldspurgerZelevinskySocle
import Langlands.Representation.Classification.SegmentHeadCutEmbedding
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.LanglandsSubrepresentationStatement

/-!
# Products of segment heads along lists of intervals

Rank-zero units on both sides, associativity allowing rank-zero irreducible factors, chosen
Langlands heads of realized intervals, their right-nested products along a list of intervals,
and the corresponding segment-product data.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ### Rank-zero factors -/

variable (T) in
/-- Positive rank, or rank zero and irreducible. -/
abbrev PosOrIrr {m : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) : Prop :=
  0 < m ∨ (m = 0 ∧ (letI := T.topology; Y.IsIrreducible))

/-- A rank-zero irreducible left factor is a unit, up to rank transport. -/
theorem castIso_rankZero_left {w b : ℕ} (hw : w = 0)
    (W : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear w F.Carrier))
    (hW : letI := T.topology; W.IsIrreducible)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor w b).obj (W, X)) X := by
  let := T.topology
  subst hw
  have e₁ := (T.binaryNormalizedProductFunctor 0 b).mapIso
    (Iso.prod (rankZeroIrreducibleUnitIso F T W hW) (Iso.refl X))
  have e₂ := SegmentProductOrderedAssembly.leftUnitIso T X
  exact (castIso_of_iso (e₁ ≪≫ e₂)).trans (castIso_generalLinearRankCast _ X).symm

theorem CastIso.isIrreducible {r s : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear s F.Carrier)}
    (h : CastIso T X Y) (hX : letI := T.topology; X.IsIrreducible) :
    letI := T.topology; Y.IsIrreducible := by
  let := T.topology
  obtain ⟨rfl, ⟨e⟩⟩ := h
  exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e.symm)).mpr hX

/-- Associativity, allowing rank-zero irreducible middle and last factors. -/
theorem castIso_assoc'' {a b c : ℕ} (ha : 0 < a)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (C : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier))
    (hB : PosOrIrr T B) (hC : PosOrIrr T C) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor (a + b) c).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B), C))
      ((T.binaryNormalizedProductFunctor a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor b c).obj (B, C))) := by
  let := T.topology
  rcases hB with hb | ⟨hb, hBi⟩
  · exact castIso_assoc' ha hb A B C hC
  · have h1 := castIso_rankZero_right hb A B hBi
    have h2 := castIso_rankZero_left hb B hBi C
    exact (h1.binary (CastIso.refl C)).trans ((CastIso.refl A).binary h2).symm

theorem posOrIrr_binary {a b : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    (hX : PosOrIrr T X) (hY : PosOrIrr T Y) :
    PosOrIrr T (letI := T.topology; (T.binaryNormalizedProductFunctor a b).obj (X, Y)) := by
  let := T.topology
  rcases hX with ha | ⟨ha, hXi⟩
  · left; omega
  · rcases hY with hb | ⟨hb, hYi⟩
    · left; omega
    · right
      exact ⟨by omega, (castIso_rankZero_right hb X Y hYi).symm.isIrreducible hXi⟩

theorem posOrIrr_of_isIrreducible {m : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hX : letI := T.topology; X.IsIrreducible) : PosOrIrr T X := by
  rcases Nat.eq_zero_or_pos m with h | h
  · exact Or.inr ⟨h, hX⟩
  · exact Or.inl h

/-- `(B^K × Y) × Z ≅ B^K × (Y × Z)`, up to rank transport. -/
theorem castIso_iterProd_binary {r : ℕ} (hr : 0 < r)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    ∀ (K : ℕ) {m c : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      PosOrIrr T Y → PosOrIrr T Z →
      CastIso T (letI := T.topology;
          (T.binaryNormalizedProductFunctor (powerRank r K m) c).obj (iterProd T B K Y, Z))
        (iterProd T B K (letI := T.topology; (T.binaryNormalizedProductFunctor m c).obj (Y, Z)))
  | 0, _, _, _, _, _, _ => CastIso.refl _
  | K + 1, m, c, Y, Z, hY, hZ => by
    let := T.topology
    have hW := iterProd_rank_pos_or hr B K Y hY
    have h1 := castIso_assoc'' hr B (iterProd T B K Y) Z hW hZ
    have h2 := (CastIso.refl B).binary (castIso_iterProd_binary hr B K Y Z hY hZ)
    exact h1.trans h2

/-! ### Chosen heads and their products along lists -/

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

variable (F) in
/-- The chosen Langlands head of the realized segment of `I`. -/
def segHead (I : Interval) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (I.realize ρ x).degree F.Carrier) :=
  T.segmentHead (I.realize ρ x)

theorem segHead_isSegmentHead (I : Interval) :
    T.IsSegmentHead (I.realize ρ x) (segHead F ρ x I) := by
  obtain ⟨π, hπ, -⟩ := segmentSpecialConstituentExistence.{uF, max uF uV} F T (I.realize ρ x)
  exact hπ.isSegmentHead_segmentHead

theorem segHead_isIrreducible (I : Interval) :
    letI := T.topology; (segHead F ρ x I).IsIrreducible :=
  SegmentHeadSupport.isIrreducible_of_isSegmentHead T (segHead_isSegmentHead ρ x I)

theorem realize_degree_pos (I : Interval) : 0 < (I.realize ρ x).degree :=
  (I.realize ρ x).degree_pos

/-- The rank of the product of the heads along `l` with a representation of rank `m`. -/
def listRank : List Interval → ℕ → ℕ
  | [], m => m
  | I :: l, m => (I.realize ρ x).degree + listRank l m

variable (F) in
/-- `L(I₁) × (L(I₂) × ⋯ × (L(I_k) × Y))`. -/
def listProd : (l : List Interval) → {m : ℕ} →
    (letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) →
    (letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (listRank ρ x l m) F.Carrier))
  | [], _, Y => Y
  | I :: l, m, Y =>
    letI := T.topology
    (T.binaryNormalizedProductFunctor (I.realize ρ x).degree (listRank ρ x l m)).obj
      (segHead F ρ x I, listProd l Y)

variable (F) in
/-- The datum with the chosen heads along `l` followed by `d`. -/
def consHeads : (l : List Interval) → {m : ℕ} → T.SegmentProductDatum.{max uF uV, uF} m →
    T.SegmentProductDatum.{max uF uV, uF} (listRank ρ x l m)
  | [], _, d => d
  | I :: l, _, d =>
    SegmentProductOrderedAssembly.cons (I.realize ρ x) (segHead F ρ x I) (consHeads l d)

theorem consHeads_induced :
    ∀ (l : List Interval) {m : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} m),
      CastIso T (consHeads F ρ x l d).induced (listProd F ρ x l d.induced)
  | [], _, _ => CastIso.refl _
  | I :: l, m, d => by
    let := T.topology
    obtain ⟨e₀⟩ := SegmentProductOrderedAssembly.nonempty_cons_iso_binary
      (I.realize ρ x) (segHead F ρ x I) (consHeads F ρ x l d)
    exact (castIso_of_iso e₀).trans ((CastIso.refl _).binary (consHeads_induced l d))

theorem consHeads_segments :
    ∀ (l : List Interval) {m : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} m),
      List.ofFn (consHeads F ρ x l d).segments =
        l.map (Interval.realize ρ x) ++ List.ofFn d.segments
  | [], _, _ => rfl
  | I :: l, _, d => by
    show List.ofFn (SegmentProductOrderedAssembly.cons (I.realize ρ x)
      (segHead F ρ x I) (consHeads F ρ x l d)).segments = _
    rw [SegmentProductOrderedAssembly.cons_segments, consHeads_segments l d]
    rfl

theorem cons_hasSegmentHeads {n : ℕ} (Δ : T.Segment.{max uF uV, uF})
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hA : T.IsSegmentHead Δ A) (hd : d.HasSegmentHeads) :
    (SegmentProductOrderedAssembly.cons Δ A d).HasSegmentHeads := Fin.cases hA hd

theorem consHeads_hasSegmentHeads :
    ∀ (l : List Interval) {m : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} m),
      d.HasSegmentHeads → (consHeads F ρ x l d).HasSegmentHeads
  | [], _, _, h => h
  | I :: l, _, d, h =>
    cons_hasSegmentHeads _ _ _ (segHead_isSegmentHead ρ x I) (consHeads_hasSegmentHeads l d h)

theorem empty_hasSegmentHeads :
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).HasSegmentHeads :=
  fun i => i.elim0

theorem listRank_eq : ∀ (l : List Interval) (m : ℕ),
    listRank ρ x l m = weight (l : Multisegment) * ρ.rank + m
  | [], m => by simp [listRank, weight]
  | I :: l, m => by
    rw [listRank, listRank_eq l m, ← Multiset.cons_coe, weight_cons]
    show I.length * ρ.rank + (weight (l : Multisegment) * ρ.rank + m) = _
    ring

end Langlands.MoeglinWaldspurger.Derivation
