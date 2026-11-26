import Langlands.Global.Arithmetic.HarrisProposition48SpacedData
import Langlands.Galois.Harris1998MultiplicityStatement
import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement
import Langlands.Global.Arithmetic.HarrisProposition48SingletonDescentStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerRestrictedDescentStatement

/-!
# Harris's Proposition 4.8 with Theorem 1.2 with multiplicity as input

Beside each statement of the induction for Harris (1998), Proposition 4.8, that takes the
published `Harris1998Theorem12CuspidalStatement` as an input, the statement that takes
Harris's Theorem 1.2 with multiplicity in Henniart's form
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in its place. The new premise is
stated only over base fields of even real degree and for classes of regular highest
weight, so the problems and data carry the two clauses of `IsSpaced` and `IsProposition48SpacedDatum`
(module `HarrisProposition48SpacedData`). The published statements are unchanged.
Proposition definitions, with the two implications between the conclusions.
-/

noncomputable section

universe uF uE uE' uL uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure

/-- Harris 1998, Proposition 4.8, for the data with even real degree and weights at
distance at least two: `Proposition48Statement` with `IsProposition48SpacedDatum` in place
of `IsProposition48Datum`; nothing else is changed. -/
def Proposition48SpacedStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
    [IsCMField E] [IsCMField E'] [CompactSpace (AdeleQuotient E)]
    (e : ReciprocityFamily F) (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E'),
    NormalizedReciprocity F e → IsProposition48SpacedDatum e χ χs K₀ P Ps ξ →
      ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r),
        c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ ∧
        c.IsRegularAlgebraic ∧
        c.IsConjugateSelfDual ∧
        c.HasSupercuspidalComponent.{uE, uV} Ps.v

/-- The published Proposition 4.8 implies its form for the data with even real degree and
weights at distance at least two. -/
theorem proposition48SpacedStatement_of_proposition48Statement
    (h : Proposition48Statement.{uF, uE, uE', uL, uV}) :
    Proposition48SpacedStatement.{uF, uE, uE', uL, uV} := by
  intro p _ F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ e χ χs K₀ P Ps ξ he hD
  exact h F F' E E' L e χ χs K₀ P Ps ξ he hD.1

section ExactStabilizer

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {F' : Extension F}
  {E E' L : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsCMField E] [IsCMField E']

/-- The exact-stabilizer datum (`IsProposition48ExactStabilizerDatum`) with even real degree
and weights at distance at least two. -/
def IsProposition48ExactStabilizerSpacedDatum (e : ReciprocityFamily F)
    (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E') : Prop :=
  IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ ∧ HasEvenRealDegree E ∧
    IsRelativelySpaced E ξ

end ExactStabilizer

/-- `Proposition48ExactStabilizerStatement` with `IsProposition48ExactStabilizerSpacedDatum`
in place of `IsProposition48ExactStabilizerDatum`; nothing else is changed. -/
def Proposition48ExactStabilizerSpacedStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
    [IsCMField E] [IsCMField E'] [CompactSpace (AdeleQuotient E)]
    (e : ReciprocityFamily F) (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E'),
    NormalizedReciprocity F e → IsProposition48ExactStabilizerSpacedDatum e χ χs K₀ P Ps ξ →
      ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r),
        c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ ∧
        c.IsRegularAlgebraic ∧
        c.IsConjugateSelfDual ∧
        c.HasSupercuspidalComponent.{uE, uV} Ps.v

/-- The spaced form of Proposition 4.8 implies its spaced exact-stabilizer form, because the
exact-stabilizer datum implies the published datum. -/
theorem proposition48ExactStabilizerSpacedStatement_of_proposition48SpacedStatement
    (h : Proposition48SpacedStatement.{uF, uE, uE', uL, uV}) :
    Proposition48ExactStabilizerSpacedStatement.{uF, uE, uE', uL, uV} := by
  intro p _ F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ e χ χs K₀ P Ps ξ he hD
  exact h F F' E E' L e χ χs K₀ P Ps ξ he ⟨hD.1.isProposition48Datum, hD.2⟩

section Branches

open Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- `Proposition48PrimeBranchStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48MultiplicityPrimeBranchStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicRegularInductionStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV}

/-- `Proposition48SingletonBranchStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48MultiplicitySingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV}

/-- `Proposition48PrimeBranchTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48MultiplicityPrimeBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicRegularInductionTCStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV}

/-- `Proposition48SingletonBranchTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48MultiplicitySingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV}

/-- `Proposition48ExactStabilizerPrimeBranchStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerMultiplicityPrimeBranchStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicRegularInductionStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerSingletonBranchStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerMultiplicitySingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
  CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerPrimeBranchTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicRegularInductionTCStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerSingletonBranchTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerMultiplicitySingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
  CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, for problems that also satisfy `IsSpaced` (even
real degree and weights at distance at least two). The other premises and the body are
unchanged. -/
def Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsSpaced → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

end Branches

section Descent

open Langlands.Automorphic.Unramified Langlands.GaloisRepresentation
open Langlands.LocalFactor.Archimedean AdelicFunctoriality

/-- `Proposition48SingletonDescentSelectionTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`. The problem is required to satisfy `IsSpaced` (even
real degree and weights at distance at least two), and the descents of `S` are assumed to
have regular highest weight (`HasRegularHighestWeight`, which implies the published
`IsRegularAlgebraic`) and a supercuspidal component at the auxiliary place. The rank is at
least two (`1 ≤ r`), as Theorem 1.2 with multiplicity excludes rank one. The rest is
unchanged. -/
def Proposition48MultiplicitySingletonDescentSelectionTCStatement : Prop :=
  Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
      letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
      ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r), 1 ≤ r →
        ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        S.isoClass.IsConjugateSelfDual →
        Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
        (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
        (∀ c : CuspidalOperatorRealization.IsoClass Q.E r,
          CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
            S.isoClass c →
          c.HasRegularHighestWeight ∧ c.HasSupercuspidalComponent.{0, uV} Q.Ps.v) →
        ∃ c : CuspidalOperatorRealization.IsoClass Q.E r,
          CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
            S.isoClass c ∧
          c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ

end Descent

section Reductions

open Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- `Proposition48ReductionStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48SpacedStatement`). The other inputs are unchanged. -/
def Proposition48MultiplicityReductionStatement : Prop :=
  (Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48MultiplicityPrimeBranchStatement.{uF, uV} ∧
    Proposition48MultiplicitySingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}) →
  Proposition48SpacedStatement.{uF, 0, 0, 0, uV}

/-- `Proposition48ReductionTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48SpacedStatement`). The other inputs are unchanged. -/
def Proposition48MultiplicityReductionTCStatement : Prop :=
  (Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48MultiplicityPrimeBranchTCStatement.{uF, uV} ∧
    Proposition48MultiplicitySingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV}) →
  Proposition48SpacedStatement.{uF, 0, 0, 0, uV}

/-- `Proposition48ExactStabilizerReductionStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48ExactStabilizerSpacedStatement`). The other inputs are unchanged. -/
def Proposition48ExactStabilizerMultiplicityReductionStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicityPrimeBranchStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicitySingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} ∧
    CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerSpacedStatement.{uF, 0, 0, 0, uV}

/-- `Proposition48ExactStabilizerReductionTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48ExactStabilizerSpacedStatement`). The other inputs are unchanged. -/
def Proposition48ExactStabilizerMultiplicityReductionTCStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicitySingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerSpacedStatement.{uF, 0, 0, 0, uV}

/-- `Proposition48ExactStabilizerRestrictedReductionStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48ExactStabilizerSpacedStatement`). The other inputs are unchanged. -/
def Proposition48ExactStabilizerRestrictedMultiplicityReductionStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicityPrimeBranchStatement.{uF, uV} ∧
    Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerSpacedStatement.{uF, 0, 0, 0, uV}

/-- `Proposition48ExactStabilizerRestrictedReductionTCStatement` with Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of the published
`Harris1998Theorem12CuspidalStatement`, the two branch inputs replaced by their forms with
that premise, and the conclusion restricted to the data with even real degree and weights
at distance at least two (`Proposition48ExactStabilizerSpacedStatement`). The other inputs are unchanged. -/
def Proposition48ExactStabilizerRestrictedMultiplicityReductionTCStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerSpacedStatement.{uF, 0, 0, 0, uV}

end Reductions

end Langlands.Global.Harris
