import Langlands.Representation.Derivative.LeibnizConstituentExtraction
import Langlands.Representation.Induction.BinaryProductConstituentExtraction
import Langlands.Representation.CuspidalSupport.BinaryProductSupport

/-! Actual factor constituents and supplied support aggregation in Leibniz pieces. -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.BinaryDerivativeSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Actual irreducible factor constituents at one feasible derivative-order pair,
with a literal presentation of the supplied constituent in their product. -/
structure FactorData {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier)) where
  index : LeibnizIndex a b d
  left : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a - index.val.1) F.Carrier)
  right : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b - index.val.2) F.Carrier)
  left_irreducible : letI := T.topology; left.IsIrreducible
  left_occurs : letI := T.topology
    SmoothRep.IsSubquotient left
      ((generalLinearDerivative T ψ a index.val.1
        (leibnizIndices_left_le index.property)).obj A)
  right_irreducible : letI := T.topology; right.IsIrreducible
  right_occurs : letI := T.topology
    SmoothRep.IsSubquotient right
      ((generalLinearDerivative T ψ b index.val.2
        (leibnizIndices_right_le index.property)).obj B)
  subspace : letI := T.topology
    Subrepresentation
      ((generalLinearRankCast T (leibnizIndices_rank index.property)).obj
        ((T.binaryNormalizedProductFunctor (a - index.val.1) (b - index.val.2)).obj
          (left, right))).representation
  kernel : letI := T.topology
    Subrepresentation (SmoothRep.subrepresentation
      ((generalLinearRankCast T (leibnizIndices_rank index.property)).obj
        ((T.binaryNormalizedProductFunctor (a - index.val.1) (b - index.val.2)).obj
          (left, right))) subspace).representation
  occurrenceIso : letI := T.topology
    D ≅ SmoothRep.subquotient
      ((generalLinearRankCast T (leibnizIndices_rank index.property)).obj
        ((T.binaryNormalizedProductFunctor (a - index.val.1) (b - index.val.2)).obj
          (left, right))) subspace kernel

private theorem rankCast_factor_extraction {a b r : ℕ} (h : a + b = r)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; A.HasFiniteLength)
    (hB : letI := T.topology; B.HasFiniteLength)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) :
    letI := T.topology
    ∃ (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (H : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      E.IsIrreducible ∧ SmoothRep.IsSubquotient E A ∧
      H.IsIrreducible ∧ SmoothRep.IsSubquotient H B ∧
      SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (E, H))) := by
  cases h
  exact T.exists_irreducible_factor_subquotients_of_binaryProduct A B hA hB D hD hDP

private theorem factorData_nonempty_of_piece {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology
      ∀ i (hi : i ≤ a), ((generalLinearDerivative T ψ a i hi).obj A).HasFiniteLength)
    (hB : letI := T.topology
      ∀ j (hj : j ≤ b), ((generalLinearDerivative T ψ b j hj).obj B).HasFiniteLength)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hpiece : letI := T.topology
      ∃ x : LeibnizIndex a b d,
        SmoothRep.IsSubquotient D ((leibnizSmoothPiece T ψ a b d x).obj (A, B))) :
    Nonempty (FactorData T ψ A B D) := by
  let := T.topology
  obtain ⟨x, hx⟩ := hpiece
  obtain ⟨E, H, hE, hEA, hH, hHB, hDP⟩ :=
    rankCast_factor_extraction T (leibnizIndices_rank x.property) _ _
      (hA _ _) (hB _ _) D hD hx
  obtain ⟨S, K, ⟨e⟩⟩ := hDP
  exact ⟨⟨x, E, H, hE, hEA, hH, hHB, S, K, e⟩⟩

/-- Choose actual irreducible factor constituents for an irreducible constituent
of a binary-product derivative, assuming finite length of the factor derivatives. -/
def factorData {a b d : ℕ} (hd : d ≤ a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology
      ∀ i (hi : i ≤ a), ((generalLinearDerivative T ψ a i hi).obj A).HasFiniteLength)
    (hB : letI := T.topology
      ∀ j (hj : j ≤ b), ((generalLinearDerivative T ψ b j hj).obj B).HasFiniteLength)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology
      SmoothRep.IsSubquotient D
        ((generalLinearDerivative T ψ (a + b) d hd).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) :
    FactorData T ψ A B D :=
  Classical.choice (factorData_nonempty_of_piece T ψ A B hA hB D hD
    (exists_leibnizSmoothPiece_subquotient T ψ hd A B D hD hDA))

/-- The same actual construction when a supplied subquotient is taken before
differentiating the source binary product. -/
def factorDataOfSubquotient {a b d : ℕ} (hd : d ≤ a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology
      ∀ i (hi : i ≤ a), ((generalLinearDerivative T ψ a i hi).obj A).HasFiniteLength)
    (hB : letI := T.topology
      ∀ j (hj : j ≤ b), ((generalLinearDerivative T ψ b j hj).obj B).HasFiniteLength)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier))
    (hQ : letI := T.topology
      SmoothRep.IsSubquotient Q ((T.binaryNormalizedProductFunctor a b).obj (A, B)))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ (a + b) d hd).obj Q)) :
    FactorData T ψ A B D :=
  Classical.choice (factorData_nonempty_of_piece T ψ A B hA hB D hD (by
    let := T.topology
    obtain ⟨x, _, _, hx⟩ :=
      exists_leibnizSmoothPiece_subquotient_of_subquotient T ψ hd A B Q hQ D hD hDQ
    exact ⟨x, hx⟩))

private theorem rankCast_binary_support {a b r : ℕ} (h : a + b = r)
    {E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {H : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    {s t : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T)}
    (hE : T.IsSupercuspidalSupport E s)
    (hH : T.IsSupercuspidalSupport H t)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (E, H)))) :
    T.IsSupercuspidalSupport D (s + t) := by
  cases h
  exact T.binaryProductConstituentSupport hE hH hD hDP

/-- Original-universe support witnesses for the actual factor constituents,
their supplied predicates, and a support of the original constituent. -/
structure SupportData {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (PL PR : ℕ → Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop)
    extends FactorData T ψ A B D where
  leftSupport : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T)
  rightSupport : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T)
  left_support : T.IsSupercuspidalSupport left leftSupport
  right_support : T.IsSupercuspidalSupport right rightSupport
  left_allowed : PL index.val.1 leftSupport
  right_allowed : PR index.val.2 rightSupport
  support : T.IsSupercuspidalSupport D (leftSupport + rightSupport)

/-- Aggregate supplied support bounds on simple factor-derivative constituents
using their actual occurrences, with the original datum universe unchanged. -/
def supportData {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (f : FactorData T ψ A B D)
    (PL PR : ℕ → Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop)
    (hA : letI := T.topology
      ∀ i (hi : i ≤ a)
        (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a - i) F.Carrier)),
        E.IsIrreducible →
        SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ a i hi).obj A) →
        ∃ s, PL i s ∧ T.IsSupercuspidalSupport E s)
    (hB : letI := T.topology
      ∀ j (hj : j ≤ b)
        (H : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b - j) F.Carrier)),
        H.IsIrreducible →
        SmoothRep.IsSubquotient H ((generalLinearDerivative T ψ b j hj).obj B) →
        ∃ t, PR j t ∧ T.IsSupercuspidalSupport H t) :
    SupportData T ψ A B D PL PR := by
  let := T.topology
  have hs := hA f.index.val.1 (leibnizIndices_left_le f.index.property)
    f.left f.left_irreducible f.left_occurs
  have ht := hB f.index.val.2 (leibnizIndices_right_le f.index.property)
    f.right f.right_irreducible f.right_occurs
  let s := Classical.choose hs
  let t := Classical.choose ht
  have hsum := rankCast_binary_support T (leibnizIndices_rank f.index.property)
    (Classical.choose_spec hs).2 (Classical.choose_spec ht).2 hD
    ⟨f.subspace, f.kernel, ⟨f.occurrenceIso⟩⟩
  exact
    { toFactorData := f
      leftSupport := s
      rightSupport := t
      left_support := (Classical.choose_spec hs).2
      right_support := (Classical.choose_spec ht).2
      left_allowed := (Classical.choose_spec hs).1
      right_allowed := (Classical.choose_spec ht).1
      support := hsum }

end Langlands.Derivative.BinaryDerivativeSupport
