import Langlands.BaseChange.SigmaDiscreteRegularDescentStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Forward
import Langlands.BaseChange.SigmaLiftCharacterIdentityReverse

/-!
# The regular σ-lift identity implies the σ-lift identity

Henniart–Lemaire (2011), II.2.9 (pp. 69–71) and II.6.13 (pp. 129–130),
pass from the trace identity on regularly supported concordant pairs to a σ-lift.
See also Arthur–Clozel (1989), Chapter 1, §6.3 (p. 57). The proposition below
uses the norm-determinant support condition of `IsRegularSigmaLift` and the
analytic and transfer premises of the two Library character identity statements.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- Under the premises of `SigmaLiftCharacterIdentityForwardStatement` and
`SigmaLiftCharacterIdentityReverseStatement`, the regular σ-lift identity for
irreducible admissible representations over a characteristic-zero nonarchimedean
local field and a cyclic algebra implies the σ-lift identity for the same
intertwiner and scalar. -/
def RegularSigmaLiftUpgradeStatement.{u, v, uV, uW} : Prop :=
  TwistedCharacterRegularValuesStatement.{u, u, uV} →
  TwistedCharacterRegularValuesStatement.{u, v, uW} →
  RegularTransferStatement.{u, v} →
  ConcordantIntegralEqualityStatement.{u, v} →
  SigmaLiftCharacterIdentity.SigmaRegularOpenStatement.{u, v} →
  ConcordantIntegrableIntegralEqualityStatement.{u, v} →
  CharacterLocalIntegrabilityStatement.{u, uV} →
  TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (c : ℂ),
        IsRegularSigmaLift σ l π hπ τ hτ A c → IsSigmaLift σ l π hπ τ hτ A c

end Langlands.BaseChange
