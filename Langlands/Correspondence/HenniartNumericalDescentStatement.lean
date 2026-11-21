import Langlands.Correspondence.HenniartCompatibleInjections
import Langlands.Correspondence.HenniartGLUpperBoundStatement
import Langlands.Correspondence.HenniartLaumonDeligneStatement

/-!
# Slope bounds and descent for Henniart's numerical correspondence

The statements of `lem:slopebc`, `lem:step` and `thm:descent` from Option II
of the numerical local Langlands route note, using weak cyclic base change
and rank-bounded compatible numerical injections. No proofs are included.
-/

namespace Langlands.Henniart

open Correspondence Numerical

/-- A supercuspidal class of slope at most `x` has all its base-change
constituents of slope at most `ψ_{M/L}(x)` (route note, `lem:slopebc`). -/
def BaseChangeSlopeStatement.{uK, uV} : Prop :=
  SupercuspidalTwistSwanBoundStatement.{uK, uV} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p) (Ch : CyclicBaseChangeMap.{uK, uV} S),
      IsWeakCyclicBaseChange S Ch →
        ∀ (k : ℕ) (π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
          (x : ℝ) (s : ℕ),
          HasSupercuspidalSwan S.base π s → (s : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * x →
            ∀ ρ ∈ Ch k π,
              (supercuspidalSwanExponent S.top ρ.2 : ℝ) ≤
                ((ρ.1 + 1 : ℕ) : ℝ) * S.herbrandPsi x

/-- Equal refined counts descend through one cyclic prime-degree step,
from slope `ψ_{M/L}(x)` over `M` to `x` over `L`, with compatible injections
in ranks at most `N` (route note, `lem:step`). -/
def DescentStepStatement.{uK, uW, uV} : Prop :=
  SupercuspidalTwistSwanBoundStatement.{uK, uV} → WeilArtinConductorExistenceStatement.{uK, uW} →
    ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p) (N : ℕ)
      (φL : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.base k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
      (φM : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.top k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat)
      (Ch : CyclicBaseChangeMap.{uK, uV} S),
      (∀ (k : ℕ) (hk : k + 1 ≤ N),
        IsNumericalInjection S.base (φL k hk) ∧ IsNumericalInjection S.top (φM k hk)) →
      IsWeakCyclicBaseChange S Ch → IsBaseChangeCompatible S Ch N φL φM →
      ReflectsGaloisInvariance S N φM →
        ∀ x : ℝ, CountsAgreeUpToSlope.{uK, uW, uV} S.top (S.herbrandPsi x) N →
          CountsAgreeUpToSlope.{uK, uW, uV} S.base x N

/-- The conditional assembly of Option II (route note, `thm:descent`):
(I1), (LD), (I4), the twist Swan bound and Artin conductor existence give
equal refined counts at every slope and rank bound, numerical surjectivity,
and equal finite orbit counts by conductor. -/
def NumericalDescentStatement.{uK, uW, uV} : Prop :=
  SupercuspidalStratumUpperBoundStatement.{uK, uV} → LaumonDeligneCountStatement.{uK, uW} →
  CompatibleNumericalInjectionsStatement.{uK, uW, uV} → SupercuspidalTwistSwanBoundStatement.{uK, uV} →
  WeilArtinConductorExistenceStatement.{uK, uW} →
    (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (x : ℝ) (N : ℕ),
      CountsAgreeUpToSlope.{uK, uW, uV} K x N) ∧
    NumericalSurjectivityStatement.{uK, uW, uV} ∧ NumericalOrbitCountStatement.{uK, uW, uV}

end Langlands.Henniart
