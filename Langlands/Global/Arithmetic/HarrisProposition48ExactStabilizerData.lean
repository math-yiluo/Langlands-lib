import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.Arithmetic.GeneralPositionOfExactStabilizerProof

/-!
# Proposition 4.8 under the exact Weil stabilizer condition: datum and validity

Harris (1998), Proposition 4.8 (page 201) with the auxiliary character
subject to his condition (4.12) (proof of Lemma 4.7, page 204) in place of
general position. Each definition is a published one with exactly one
conjunct changed: `IsInGeneralPosition F F' (weilCharacter F e F' χs)` becomes
`GeneralPosition.HasExactWeilStabilizer F F' (weilCharacter F e F' χs)`.
The published definitions are unchanged. The lemmas at the end pass back to
the published predicates through the proved theorem
`generalPositionOfExactStabilizer`.
-/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain
open LocalFactor.CommonClosure GeneralPosition AdelicFunctoriality

section Datum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {F' : Extension F}
variable {E E' L : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
variable [IsCMField E] [IsCMField E']

/-- The hypotheses of Harris 1998, Proposition 4.8, with the auxiliary
character subject to Harris's condition (4.12) (proof of Lemma 4.7, page 204):
the stabilizer in `W_F` of the restriction of the Weil character of `χs` to
the Weil group of `F̃` is exactly `W_{F'}`. This is `IsProposition48Datum`
with the single conjunct `IsInGeneralPosition F F' (weilCharacter F e F' χs)`
replaced by `HasExactWeilStabilizer F F' (weilCharacter F e F' χs)`; all
other conjuncts, in the same order, are unchanged. -/
def IsProposition48ExactStabilizerDatum (e : ReciprocityFamily F)
    (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E') : Prop :=
  IsSplitImaginaryQuadratic p K₀ ∧
  IsScalarTower E E' L ∧ IsNormalClosure E E' L ∧
  (p : 𝓞 E) ∈ P.v.asIdeal ∧ P.IsCompatible ∧
  HasUniquePlaceAbove L P.v ∧ HasUniquePlaceAbove L (conjPlace E P.v) ∧
  (p : 𝓞 E) ∈ Ps.v.asIdeal ∧ Ps.IsCompatible ∧
  HasUniquePlaceAbove L Ps.v ∧ HasUniquePlaceAbove L (conjPlace E Ps.v) ∧
  Ps.v ≠ P.v ∧ Ps.v ≠ conjPlace E P.v ∧
  GeneralPosition.HasExactWeilStabilizer F F' (weilCharacter F e F' χs) ∧
  IsAlgebraicAfterTwist (Module.finrank E E' - 1) ξ ∧ IsRelativelyRegular E ξ ∧
  IsConjugateInverse ξ ∧
  P.HasComponent ξ χ ∧ Ps.HasComponent ξ χs

/-- The exact-stabilizer datum implies the published general-position datum,
by the proved implication (4.12) ⇒ general position. -/
theorem IsProposition48ExactStabilizerDatum.isProposition48Datum
    {e : ReciprocityFamily F} {χ χs : FieldCharacter F F'} {K₀ : IntermediateField ℚ E}
    {P Ps : PlaceDatum F F' E E' L} {ξ : HeckeCharacter E'}
    (h : IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ) :
    IsProposition48Datum e χ χs K₀ P Ps ξ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇,
    h₁₈, h₁₉⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃,
    generalPositionOfExactStabilizer p F F' _ h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩

end Datum

namespace Proposition48Problem

/-- The two premises of the restated proposition: `IsValid` with
`IsProposition48ExactStabilizerDatum` in place of `IsProposition48Datum`. -/
def IsExactStabilizerValid (Q : Proposition48Problem.{uF}) : Prop :=
  NormalizedReciprocity Q.F Q.e ∧
    IsProposition48ExactStabilizerDatum Q.e Q.χ Q.χs Q.K₀ Q.P Q.Ps Q.ξ

/-- `IsValidAtParity` with the single conjunct
`IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)` replaced by
`HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)`. -/
def IsExactStabilizerValidAtParity (Q : Proposition48Problem.{uF}) (b : ℕ) : Prop :=
  NormalizedReciprocity Q.F Q.e ∧
  IsSplitImaginaryQuadratic Q.p Q.K₀ ∧
  IsScalarTower Q.E Q.E' Q.L ∧ IsNormalClosure Q.E Q.E' Q.L ∧
  (Q.p : 𝓞 Q.E) ∈ Q.P.v.asIdeal ∧ Q.P.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.P.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.P.v) ∧
  (Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal ∧ Q.Ps.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.Ps.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v) ∧
  Q.Ps.v ≠ Q.P.v ∧ Q.Ps.v ≠ conjPlace Q.E Q.P.v ∧
  GeneralPosition.HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs) ∧
  IsAlgebraicAfterTwist b Q.ξ ∧ IsRelativelyRegular Q.E Q.ξ ∧
  IsConjugateInverse Q.ξ ∧ Q.P.HasComponent Q.ξ Q.χ ∧ Q.Ps.HasComponent Q.ξ Q.χs

/-- `IsAuxiliaryValidAtParity` with the single conjunct
`IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)` replaced by
`HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)`.
As there, the unused primary place and character impose no condition. -/
def IsAuxiliaryExactStabilizerValidAtParity (Q : Proposition48Problem.{uF}) (b : ℕ) :
    Prop :=
  NormalizedReciprocity Q.F Q.e ∧
  IsSplitImaginaryQuadratic Q.p Q.K₀ ∧
  IsScalarTower Q.E Q.E' Q.L ∧ IsNormalClosure Q.E Q.E' Q.L ∧
  (Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal ∧ Q.Ps.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.Ps.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v) ∧
  GeneralPosition.HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs) ∧
  IsAlgebraicAfterTwist b Q.ξ ∧ IsRelativelyRegular Q.E Q.ξ ∧
  IsConjugateInverse Q.ξ ∧ Q.Ps.HasComponent Q.ξ Q.χs

/-- The one-place exact-stabilizer hypotheses at the original rank parity,
the counterpart of `IsAuxiliaryValid`. -/
def IsAuxiliaryExactStabilizerValid (Q : Proposition48Problem.{uF}) : Prop :=
  Q.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1)

/-- Exact-stabilizer validity implies the published validity. -/
theorem IsExactStabilizerValid.isValid {Q : Proposition48Problem.{uF}}
    (h : Q.IsExactStabilizerValid) : Q.IsValid :=
  ⟨h.1, h.2.isProposition48Datum⟩

/-- Exact-stabilizer validity at a parity implies the published validity at
that parity. -/
theorem IsExactStabilizerValidAtParity.isValidAtParity {Q : Proposition48Problem.{uF}}
    {b : ℕ} (h : Q.IsExactStabilizerValidAtParity b) : Q.IsValidAtParity b := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆,
    h₁₇, h₁₈, h₁₉⟩ := h
  exact ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃,
    generalPositionOfExactStabilizer Q.p Q.F Q.F' _ h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩

/-- One-place exact-stabilizer validity at a parity implies the published
one-place validity at that parity. -/
theorem IsAuxiliaryExactStabilizerValidAtParity.isAuxiliaryValidAtParity
    {Q : Proposition48Problem.{uF}} {b : ℕ}
    (h : Q.IsAuxiliaryExactStabilizerValidAtParity b) : Q.IsAuxiliaryValidAtParity b := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
  exact ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    generalPositionOfExactStabilizer Q.p Q.F Q.F' _ h₈, h₉, h₁₀, h₁₁, h₁₂⟩

/-- One-place exact-stabilizer validity implies the published one-place
validity. -/
theorem IsAuxiliaryExactStabilizerValid.isAuxiliaryValid {Q : Proposition48Problem.{uF}}
    (h : Q.IsAuxiliaryExactStabilizerValid) : Q.IsAuxiliaryValid :=
  IsAuxiliaryExactStabilizerValidAtParity.isAuxiliaryValidAtParity h

end Proposition48Problem

end Langlands.Global.Harris
