import Langlands.AllFieldBZ.Representation.Derivative.LeibnizQuotientPiece
import Langlands.AllFieldBZ.Representation.Derivative.LeibnizRestrictionExact
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.Representation.Derivative.LeibnizPositiveGluing

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizPositiveGluing`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizPositiveGluing` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSource_glued_pos leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
universe uF uV uC vC uι

variable {F : LocalFieldPackage.{uF}}

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

end Langlands.AllFieldBZ.Derivative
