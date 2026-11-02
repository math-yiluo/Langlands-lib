import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Derivative.ProductVanishing
import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Actual irreducible subquotients of the derivative Leibniz pieces. -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The actual smooth functor underlying the published Leibniz piece, retaining
both factor derivatives, the binary product, and its prescribed rank cast. -/
def leibnizSmoothPiece (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) := by
  letI := T.topology
  exact (generalLinearDerivative T ψ a x.val.1 (leibnizIndices_left_le x.property)).prod
      (generalLinearDerivative T ψ b x.val.2 (leibnizIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor (a - x.val.1) (b - x.val.2) ⋙
    generalLinearRankCast T (leibnizIndices_rank x.property)

@[simp]
theorem leibnizSmoothPiece_toRep (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    leibnizSmoothPiece.{uF, uV} T ψ a b d x ⋙ SmoothRep.toRep =
      leibnizPiece T ψ a b d x := by
  let _ := T.topology
  rfl

/-- Every irreducible actual subquotient of the derivative of a binary product
occurs in an actual smooth Leibniz piece. No finite-length hypothesis is needed. -/
theorem exists_leibnizSmoothPiece_subquotient
    {a b d : ℕ} (hd : d ≤ a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology
      SmoothRep.IsSubquotient D
        ((generalLinearDerivative T ψ (a + b) d hd).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) :
    letI := T.topology
    ∃ x : LeibnizIndex a b d,
      SmoothRep.IsSubquotient D ((leibnizSmoothPiece T ψ a b d x).obj (A, B)) := by
  let _ := T.topology
  obtain ⟨e, s, hs⟩ :=
    (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T).filtration T ψ a b d hd
  let t := ObjectRepFiltration.ofSubrepresentations
    (fun i => (s.step i).obj (A, B)) (s.monotone (A, B))
    (s.zero (A, B)) (s.top (A, B))
  obtain ⟨j, hj⟩ := t.exists_smoothGradedObject_subquotient hD hDA
  obtain ⟨ej⟩ := hs j
  have eG : (t.smoothGradedObject j).representation.Equiv
      ((leibnizSmoothPiece T ψ a b d (e.symm j)).obj (A, B)).representation :=
    Representation.equivOfIso (ej.app (A, B))
  exact ⟨e.symm j, hj.of_iso_right (SmoothRep.mkIso eG)⟩

private theorem nontrivial_of_irreducible_subquotient
    {n : ℕ}
    {A D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology; SmoothRep.IsSubquotient D A) : Nontrivial A := by
  let _ := T.topology
  apply not_subsingleton_iff_nontrivial.mp
  intro hA
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  have hDz : Subsingleton D := ⟨fun d e => by
    obtain ⟨x, rfl⟩ := hq d
    obtain ⟨y, rfl⟩ := hq e
    exact congrArg (SmoothRep.hom q) (hi (hA.elim _ _))⟩
  let : D.representation.IsIrreducible := hD
  exact (not_nontrivial_iff_subsingleton.mpr hDz)
    (IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      D.representation.asModule)

private theorem rankCast_subsingleton {m n : ℕ} (h : m = n)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hA : Subsingleton A) :
    letI := T.topology; Subsingleton ((generalLinearRankCast T h).obj A) := by
  subst n
  exact hA

/-- The piece containing an irreducible constituent has two nonzero derivative
factors, including when either residual rank is zero. -/
theorem exists_nontrivial_leibnizSmoothPiece_subquotient
    {a b d : ℕ} (hd : d ≤ a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDA : letI := T.topology
      SmoothRep.IsSubquotient D
        ((generalLinearDerivative T ψ (a + b) d hd).obj
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)))) :
    letI := T.topology
    ∃ x : LeibnizIndex a b d,
      Nontrivial ((generalLinearDerivative T ψ a x.val.1
        (leibnizIndices_left_le x.property)).obj A) ∧
      Nontrivial ((generalLinearDerivative T ψ b x.val.2
        (leibnizIndices_right_le x.property)).obj B) ∧
      SmoothRep.IsSubquotient D ((leibnizSmoothPiece T ψ a b d x).obj (A, B)) := by
  let _ := T.topology
  obtain ⟨x, hx⟩ := exists_leibnizSmoothPiece_subquotient T ψ hd A B D hD hDA
  have hP := nontrivial_of_irreducible_subquotient T hD hx
  have hnz :
      ¬ (Subsingleton ((generalLinearDerivative T ψ a x.val.1
            (leibnizIndices_left_le x.property)).obj A) ∨
        Subsingleton ((generalLinearDerivative T ψ b x.val.2
            (leibnizIndices_right_le x.property)).obj B)) := by
    intro hz
    have hzP := rankCast_subsingleton T (leibnizIndices_rank x.property) _
      (ProductVanishing.subsingleton_binary T
        (((generalLinearDerivative T ψ a x.val.1
            (leibnizIndices_left_le x.property)).obj A),
          ((generalLinearDerivative T ψ b x.val.2
            (leibnizIndices_right_le x.property)).obj B)) hz)
    exact (not_nontrivial_iff_subsingleton.mpr hzP) hP
  exact ⟨x, not_subsingleton_iff_nontrivial.mp (fun h => hnz (Or.inl h)),
    not_subsingleton_iff_nontrivial.mp (fun h => hnz (Or.inr h)), hx⟩

/-- The same extraction applies after taking any actual subquotient of the
source binary product and then any irreducible subquotient of its derivative. -/
theorem exists_leibnizSmoothPiece_subquotient_of_subquotient
    {a b d : ℕ} (hd : d ≤ a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier))
    (hQ : letI := T.topology
      SmoothRep.IsSubquotient Q ((T.binaryNormalizedProductFunctor a b).obj (A, B)))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ (a + b) d hd).obj Q)) :
    letI := T.topology
    ∃ x : LeibnizIndex a b d,
      Nontrivial ((generalLinearDerivative T ψ a x.val.1
        (leibnizIndices_left_le x.property)).obj A) ∧
      Nontrivial ((generalLinearDerivative T ψ b x.val.2
        (leibnizIndices_right_le x.property)).obj B) ∧
      SmoothRep.IsSubquotient D ((leibnizSmoothPiece T ψ a b d x).obj (A, B)) := by
  let _ := T.topology
  have hJ := generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (a + b) d hd
  have hQ' := ExactSmoothTransport.map_isSubquotient _ hJ hQ
  exact exists_nontrivial_leibnizSmoothPiece_subquotient T ψ hd A B D hD
    (smoothSubquotientTransitivity ℂ _ _ _ _ hDQ hQ')

end Langlands.Derivative
