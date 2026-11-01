import Langlands.Representation.Derivative.LeibnizRestrictionExact
import Langlands.Representation.Derivative.LeibnizQuotientPiece
import Langlands.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.Representation.Filtration.GluedFamily

/-!
# The positive-rank Leibniz gluing from the mixed-product formulas

For ranks `m + 1`, `n + 1` and a positive order `d`, the literal Leibniz source is
glued from the complete family of Leibniz grades, given the natural isomorphism and
vanishing propositions of BZ77 4.14(a) and the right mixed-product filtration
proposition of BZ77 4.14(b) as explicit hypotheses. The proof splices the
differentiated mirabolic restriction sequence: its subobject is glued from the
positive-first grades and its quotient is the zero-first grade or zero.
-/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV uC vC uι

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Gluing is preserved by the equality-based rank transport of `Rep` values. -/
theorem isGluedFromFamily_repRankCast {C : Type uC} [Category.{vC} C]
    {ι : Type uι} [Fintype ι] {a b : ℕ} (h : a = b)
    {S : C ⥤ Rep.{max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {P : ι → C ⥤ Rep.{max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hS : IsGluedFromFamily S P) :
    IsGluedFromFamily (S ⋙ generalLinearRepRankCast.{uF, max uF uV} (F := F) h)
      (fun i => P i ⋙ generalLinearRepRankCast.{uF, max uF uV} (F := F) h) := by
  subst h
  exact hS

/-- The positive-first Leibniz grades indexed by the right mixed-product indices:
the grade at `x` is the Leibniz grade at `leibnizIndexSplitEquiv m (n + 1) d (Sum.inl x)`. -/
def leibnizRestrictionSubobjectPiece (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (x : RightMixedDerivativeIndex (n + 1) m d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear (((m + 1) + (n + 1)) - d) F.Carrier) :=
  leibnizPiece.{uF, uV} T ψ (m + 1) (n + 1) d (leibnizIndexSplitEquiv m (n + 1) d (Sum.inl x))

/-- The optional zero-first Leibniz grade indexed by `PLift (d ≤ n + 1)`: the grade at
`h` is the Leibniz grade at `leibnizIndexSplitEquiv m (n + 1) d (Sum.inr h)`. -/
def leibnizRestrictionQuotientPiece (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (h : PLift (d ≤ n + 1)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear (((m + 1) + (n + 1)) - d) F.Carrier) :=
  leibnizPiece.{uF, uV} T ψ (m + 1) (n + 1) d (leibnizIndexSplitEquiv m (n + 1) d (Sum.inr h))

/-- The differentiated restriction subobject is glued from the positive-first
Leibniz grades, given BZ77 4.14(b). -/
theorem leibnizRestrictionSubobject_glued (T : F.TopologicalData)
    (hRM : RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    IsGluedFromFamily (leibnizRestrictionDerivativeSubobject.{uF, uV} T ψ m n d hd)
      (leibnizRestrictionSubobjectPiece.{uF, uV} T ψ m n d) := by
  let _ := T.topology
  obtain ⟨e, he⟩ := hRM ψ (n + 1) m d (by omega)
  have h := (isGluedFromFamily_repRankCast
      (show ((n + 1) + m) + 1 - d = ((m + 1) + (n + 1)) - d by omega)
      (IsGluedFromFamily.of_isGluedFrom
        (P := rightMixedDerivativePiece T ψ (n + 1) m d) e he)).precomp
    ((generalLinearRestriction.{uF, uV} T m).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))))
  exact h.isoPieces (fun x => leibnizPositivePieceIso T ψ m (n + 1) d x)

/-- The differentiated restriction quotient is glued from the optional zero-first
Leibniz grade, given BZ77 4.14(a). -/
theorem leibnizRestrictionQuotient_glued (T : F.TopologicalData)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    IsGluedFromFamily (leibnizRestrictionDerivativeQuotient.{uF, uV} T ψ m n d hd)
      (leibnizRestrictionQuotientPiece.{uF, uV} T ψ m n d) := by
  let _ := T.topology
  by_cases hb : d ≤ n + 1
  · let _ : Unique (PLift (d ≤ n + 1)) := ⟨⟨⟨hb⟩⟩, fun _ => rfl⟩
    exact IsGluedFromFamily.of_iso_unique
      (leibnizRestrictionQuotientPieceIso T ψ m n d ⟨hd.1, hb⟩
        (Classical.choice (hLI ψ (m + 1) n d ⟨hd.1, hb⟩)))
  · let _ : IsEmpty (PLift (d ≤ n + 1)) := ⟨fun h => hb h.down⟩
    exact IsGluedFromFamily.of_isEmpty
      (leibnizRestrictionQuotient_subsingleton T ψ m n d hd
        (hLV ψ (m + 1) n d ⟨hd.1, by omega⟩ (by omega)))

/-- BZ77 4.14(c) at positive ranks and positive order, as gluing from the complete
family of Leibniz grades, given BZ77 4.14(a) and 4.14(b). -/
theorem leibnizSource_glued_pos (T : F.TopologicalData)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hRM : RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    IsGluedFromFamily (leibnizSource.{uF, uV} T ψ (m + 1) (n + 1) d hd.2)
      (leibnizPiece T ψ (m + 1) (n + 1) d) := by
  let _ := T.topology
  obtain ⟨i, q, h⟩ := leibnizRestrictionDerivativeExact T ψ m n d hd
  have hM := (leibnizRestrictionSubobject_glued T hRM ψ m n d hd).splice
    (leibnizRestrictionQuotient_glued T hLI hLV ψ m n d hd) i q
    (fun X => (h X).2.1) (fun X => (h X).1) (fun X => (h X).2.2)
  refine hM.equiv (leibnizIndexSplitEquiv m (n + 1) d) ?_
  rintro (x | x)
  · exact Iso.refl _
  · exact Iso.refl _

/-- BZ77 4.14(c) at positive ranks and positive order in the shape of the published
statement, given BZ77 4.14(a) and 4.14(b). -/
theorem generalLinearDerivativeLeibnizFiltration_pos (T : F.TopologicalData)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hRM : RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    ∃ e : LeibnizIndex (m + 1) (n + 1) d ≃ Fin (leibnizIndices (m + 1) (n + 1) d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ (m + 1) (n + 1) d hd.2)
        (fun i => leibnizPiece T ψ (m + 1) (n + 1) d (e.symm i)) := by
  let _ := T.topology
  obtain ⟨e, he⟩ := (leibnizSource_glued_pos T hLI hLV hRM ψ m n d hd).exists_equiv _
    (Fintype.card_coe _)
  exact ⟨e.symm, he⟩

end Langlands.Derivative
