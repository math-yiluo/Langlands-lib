import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.ExtensionInvariants
import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Local self-pair Euler identity for a σ-lift

Henniart–Lemaire (2011), II.4.6, Théorème (4), with the contragredient as the
second lift as in II.2.9, Remarque (5), and II.4.12. The p-adic formula is
Arthur–Clozel (1989), Chapter 1, Proposition 6.9(i).
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (UnitaryAdditiveCharacter)
open LocalFactor.PadicAbelian (SelfDualHaar)
open RankinSelberg (IsPadicRankLPolynomial)
open scoped BigOperators

/-- The certified denominator for a σ-discrete lift paired with its smooth
contragredient, after substitution by the residue degree, is the product of
the base-field denominators obtained by twisting the second action by each
norm-trivial determinant character. -/
def SigmaLiftSelfPairLFactorStatement.{u, v, uV, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := E.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := E.canonicalTopologicalData.localField
    ∀ [IsModuleTopology F.Carrier E.Carrier]
      (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l f n : ℕ),
      IsCyclicAlgebra σ l → IsResidueDegree F.Carrier E.Carrier f → 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V) (hπ : IsAdmissible π)
      (P : Representation ℂ (GeneralLinear n E.Carrier) W) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ n P) (c : ℂ),
      π.IsIrreducible → JacquetLanglands.IsSquareIntegrable π → IsSigmaDiscreteSeries σ n P →
      (haveI := LocalFieldTopology.generalLinear_t2Space F.Carrier n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n
       haveI := LocalFieldTopology.generalLinear_t2Space E.Carrier n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (νF : SelfDualHaar F.canonicalTopologicalData ψF)
      (ψE : UnitaryAdditiveCharacter E.Carrier) (νE : SelfDualHaar E.canonicalTopologicalData ψE)
      (X : Finset (F.Carrierˣ →* ℂˣ)),
      (∀ κ, κ ∈ X ↔ IsNormTrivial E.Carrier κ) →
    ∀ (Q_E : Polynomial ℂ) (Q_F : X → Polynomial ℂ),
      IsPadicRankLPolynomial E ψE νE.val P (smoothContragredient P) Q_E →
      (∀ κ : X, IsPadicRankLPolynomial F ψF νF.val π
        (twist (κ.val.comp GeneralLinear.determinant) (smoothContragredient π)) (Q_F κ)) →
      Q_E.comp (Polynomial.X ^ f) = ∏ κ : X, Q_F κ

end Langlands.BaseChange
