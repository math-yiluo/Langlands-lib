import Langlands.Global.Arithmetic.HarrisProposition48MackeyData

/-! # One auxiliary place for the internal Proposition 4.8 induction -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure
open GeneralPosition

namespace Proposition48Problem

/-- The induction uses only the designated general-position place.
The unused primary place and character in the bundle impose no condition. -/
def IsAuxiliaryValidAtParity (Q : Proposition48Problem.{uF}) (b : ℕ) : Prop :=
  NormalizedReciprocity Q.F Q.e ∧
  IsSplitImaginaryQuadratic Q.p Q.K₀ ∧
  IsScalarTower Q.E Q.E' Q.L ∧ IsNormalClosure Q.E Q.E' Q.L ∧
  (Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal ∧ Q.Ps.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.Ps.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v) ∧
  IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs) ∧
  IsAlgebraicAfterTwist b Q.ξ ∧ IsRelativelyRegular Q.E Q.ξ ∧
  IsConjugateInverse Q.ξ ∧ Q.Ps.HasComponent Q.ξ Q.χs

/-- The one-place induction hypotheses at the original rank parity. -/
def IsAuxiliaryValid (Q : Proposition48Problem.{uF}) : Prop :=
  Q.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1)

/-- Duplicate the auxiliary place into the unused primary data.
This does not assert validity of the full two-place problem. -/
def auxiliaryPadding (Q : Proposition48Problem.{uF}) : Proposition48Problem.{uF} :=
  { Q with P := Q.Ps, χ := Q.χs }

/-- The actual Mackey relation with only the auxiliary place inherited.
Padding reuses the concrete field, character and place maps of IsMackeyChild. -/
def IsAuxiliaryMackeyChild (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (R : Proposition48Problem.{uF}) : Prop :=
  Q.auxiliaryPadding.IsMackeyChild D a R.auxiliaryPadding

/-- A genuine correcting base character for the one-place induction. -/
def IsAuxiliaryParityNormalization (Q : Proposition48Problem.{uF}) (b : ℕ)
    (ν : HeckeCharacter Q.E) (χs : FieldCharacter Q.F Q.F') : Prop :=
  IsConjugateInverse ν ∧
  IsAlgebraicAfterTwist ((b + (Module.finrank Q.E Q.E' - 1)) % 2) ν ∧
  (b % 2 = (Module.finrank Q.E Q.E' - 1) % 2 → ν = 1) ∧
  (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsAuxiliaryValid

end Proposition48Problem

end Langlands.Global.Harris
