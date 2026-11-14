import Langlands.Global.Arithmetic.HarrisProposition48InductionData
import Langlands.Automorphic.HeckeDeterminantTwistStatement

/-! # Explicit parity and determinant transport in the Proposition 4.8 induction -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure
open AdelicFunctoriality GeneralPosition

namespace Proposition48Problem

/-- The original hypotheses with the infinity-type parity supplied explicitly.
All other clauses are unchanged; in particular conjugate inversion is retained. -/
def IsValidAtParity (Q : Proposition48Problem.{uF}) (b : ℕ) : Prop :=
  NormalizedReciprocity Q.F Q.e ∧
  IsSplitImaginaryQuadratic Q.p Q.K₀ ∧
  IsScalarTower Q.E Q.E' Q.L ∧ IsNormalClosure Q.E Q.E' Q.L ∧
  (Q.p : 𝓞 Q.E) ∈ Q.P.v.asIdeal ∧ Q.P.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.P.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.P.v) ∧
  (Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal ∧ Q.Ps.IsCompatible ∧
  HasUniquePlaceAbove Q.L Q.Ps.v ∧ HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v) ∧
  Q.Ps.v ≠ Q.P.v ∧ Q.Ps.v ≠ conjPlace Q.E Q.P.v ∧
  IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs) ∧
  IsAlgebraicAfterTwist b Q.ξ ∧ IsRelativelyRegular Q.E Q.ξ ∧
  IsConjugateInverse Q.ξ ∧ Q.P.HasComponent Q.ξ Q.χ ∧ Q.Ps.HasComponent Q.ξ Q.χs

/-- Change precisely the three characters, leaving all fields and place maps fixed. -/
def withCharacters (Q : Proposition48Problem.{uF}) (ξ : HeckeCharacter Q.E')
    (χ χs : FieldCharacter Q.F Q.F') : Proposition48Problem.{uF} :=
  { Q with ξ := ξ, χ := χ, χs := χs }

/-- Twist the inducing character by the norm pullback of a base character. -/
def correctedCharacter (Q : Proposition48Problem.{uF}) (ν : HeckeCharacter Q.E) :
    HeckeCharacter Q.E' :=
  Q.ξ * ν.comp (ideleClassNorm (K := Q.E) (L := Q.E'))

/-- A genuine base-character correction, including validity of the corrected
problem and triviality of the correction when the two parities agree. -/
def IsParityNormalization (Q : Proposition48Problem.{uF}) (b : ℕ)
    (ν : HeckeCharacter Q.E) (χ χs : FieldCharacter Q.F Q.F') : Prop :=
  IsConjugateInverse ν ∧
  IsAlgebraicAfterTwist ((b + (Module.finrank Q.E Q.E' - 1)) % 2) ν ∧
  (b % 2 = (Module.finrank Q.E Q.E' - 1) % 2 → ν = 1) ∧
  (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsValid

/-- The original four output properties for a supplied cuspidal class. -/
def IsSolution (Q : Proposition48Problem.{uF}) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass Q.E r) : Prop :=
  c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ ∧
    c.IsRegularAlgebraic ∧ c.IsConjugateSelfDual ∧
    c.HasSupercuspidalComponent.{0, uV} Q.Ps.v

/-- An actual untwisted constituent together with its normalized determinant
multiple. Regular algebraicity is required only of the normalized realization. -/
def IsUntwistedSolution (Q : Proposition48Problem.{uF}) (ν : HeckeCharacter Q.E)
    {r : ℕ} (S T : CuspidalOperatorRealization Q.E r) : Prop :=
  S.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ ∧
  S.isoClass.IsConjugateSelfDual ∧
  S.isoClass.HasSupercuspidalComponent.{0, uV} Q.Ps.v ∧
  T.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.correctedCharacter ν) ∧
  T.isoClass.IsRegularAlgebraic ∧ T.isoClass.IsConjugateSelfDual ∧
  T.isoClass.HasSupercuspidalComponent.{0, uV} Q.Ps.v ∧
  OperatorRealization.IsDeterminantMultiple ν S.realization T.realization

end Proposition48Problem

end Langlands.Global.Harris
