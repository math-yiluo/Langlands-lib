import Langlands.Correspondence.HenniartCandidateBaseChangeCompatibilityReductionStatement
import Langlands.BaseChange.SigmaLiftOnSupercuspidals
import Langlands.BaseChange.SigmaLiftUniquenessStatement

/-!
# Reducing (CI1) for Henniart's candidate to classes of finite image

Every irreducible Weil class is an unramified twist of a unitary class of finite
image. Henniart's candidate extends to these twists as in Henniart (2000), §4.4.
To transport (CI1) across this extension, the cyclic base-change map has to
commute with unramified twists. Certification by σ-lifts gives a route to this
equivariance through Henniart–Lemaire (2011), II.2.9, Remarques (2) and (4).
The finite-image case is the global part of the reduction described in the
numerical correspondence route note, §6.5, source (b).
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

namespace Numerical

variable {p : ℕ} [Fact p.Prime]

/-- Base change commutes with unramified twists. The character with value `z` at a
uniformizer of `L` pulls back through `N_{M/L}` to the character with value
`z ^ f(M|L)` at a uniformizer of `M`. -/
def IsUnramifiedTwistEquivariant (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) : Prop :=
  ∀ (k : ℕ) (z : ℂˣ) (π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat),
    Ch k (supercuspidalUnramifiedTwist S.base k z π) =
      (Ch k π).map fun ρ =>
        (⟨ρ.1, supercuspidalUnramifiedTwist S.top ρ.1 (z ^ S.residueDegree) ρ.2⟩ :
          Σ j : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top j.succPNat)

/-- The clause of `IsCandidateBaseChangeCompatible` on Weil classes represented
by a unitary class factoring through a finite quotient of the absolute Galois
group of `L`. -/
def IsCandidateBaseChangeCompatibleOnFiniteImage (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) : Prop :=
  ∀ (k : ℕ) (hL : StableExistsAt.{uK, uW, uV, uW} S.base k.succPNat)
    (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat),
    (∃ b₀ : LocalWeil.UnitaryBasis.{uK, uW} S.base,
      b₀.val = ⟨k.succPNat, σ⟩ ∧ StableMap.IsFiniteFactoring S.base b₀) →
    ∀ (m : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)),
      IsRestrictionDecomposition S σ m →
        ∀ hm : ∀ τ ∈ m, StableExistsAt.{uK, uW, uV, uW} S.top τ.1.succPNat,
          Ch k (Extension.rankExtension S.base hL σ) =
            m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm

end Numerical

open Numerical

/-- Candidate existence reduces (CI1) to the classes of finite image for every map
that commutes with unramified twists. -/
def CandidateBaseChangeTwistReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
      (Ch : CyclicBaseChangeMap.{uK, uV} S),
      IsUnramifiedTwistEquivariant S Ch →
        IsCandidateBaseChangeCompatibleOnFiniteImage.{uK, uW, uV} S Ch →
          IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch

/-- Given uniqueness of σ-lifts, certification by σ-lifts on supercuspidal classes
for one `σ ≠ 1` implies equivariance under unramified twists. -/
def CertifiedCyclicBaseChangeTwistEquivarianceStatement : Prop :=
  BaseChange.SigmaLiftUniquenessStatement.{uK, uK, uV, max uK uV, max uK uV} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
      (Ch : CyclicBaseChangeMap.{uK, uV} S) (σ : S.Gal), σ ≠ 1 →
      BaseChange.IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ →
        IsUnramifiedTwistEquivariant S Ch

/-- Candidate existence implies (CI1) on classes of finite image for every weak
cyclic base change certified by σ-lifts on supercuspidal classes for every `σ ≠ 1`. -/
def CandidateFiniteImageBaseChangeCompatibilityReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
      (Ch : CyclicBaseChangeMap.{uK, uV} S),
      IsWeakCyclicBaseChange S Ch →
      (∀ σ : S.Gal, σ ≠ 1 →
        BaseChange.IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ) →
        IsCandidateBaseChangeCompatibleOnFiniteImage.{uK, uW, uV} S Ch

end Langlands.Henniart
