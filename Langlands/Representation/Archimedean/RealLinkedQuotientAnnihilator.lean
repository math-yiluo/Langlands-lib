import Langlands.Representation.Archimedean.RealLargeStandardIrreducibleReduction
import Langlands.Representation.Archimedean.MaximallyFaithfulAnnihilator

/-!
# Non-largeness of linked real Langlands quotients from a quotient with a larger annihilator

`RealLinkedStandardQuotientAnnihilatorStatement`: for a Langlands-ordered list `ds` of real
blocks of total rank `n` with two linked Mœglin data, the `O(n)`-finite functions `I(ds)` of
the standard module have a proper `(𝔤, K)`-submodule `W` and an element `u ∈ U(𝔤)` with
`u · I(ds) ⊆ W` and `u · I(ds) ≠ 0`: the annihilator of the quotient `I(ds) / W` is strictly
larger than that of `I(ds)`.

`realLinkedLanglandsQuotientNotLarge_of_quotientAnnihilator` proves that this statement,
together with the existence of an infinitesimal character on every real standard module,
implies the Library statement `RealLinkedLanglandsQuotientNotLargeStatement`. The largest
proper submodule `R` contains `W`, so `u` annihilates `I(ds) / R`. If `I(ds) / R` were
maximally faithful, the Library's `MaximallyFaithfulAnnihilator` would make `u` act by `0`
on `I(ds)`.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- **A quotient of a linked real standard module with a larger annihilator.** For a list
`ds` of real blocks of total rank `n` in Langlands order, two of whose Mœglin data are
linked, the `(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite functions of the standard module of
`ds` has a proper `(𝔤, K)`-submodule `W` and an element `u` of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` that maps
every vector into `W` but does not act by `0`. -/
def RealLinkedStandardQuotientAnnihilatorStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    ¬ IsRealMoeglinUnlinked ds →
      ∃ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W ∧ W ≠ ⊤ ∧
        ∃ u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ),
          (∀ v, envelopingAction (realStandardLie n ds) u v ∈ W) ∧
          envelopingAction (realStandardLie n ds) u ≠ 0

/-- **The reduction.** If every real standard module has an infinitesimal character and
`RealLinkedStandardQuotientAnnihilatorStatement` holds, then the Langlands quotient of a
Langlands-ordered real standard module with a linked pair of Mœglin data is not maximally
faithful. -/
theorem realLinkedLanglandsQuotientNotLarge_of_quotientAnnihilator
    (hZ : ∀ (n : ℕ) (ds : List RealBlock), HasInfinitesimalCharacter (realStandardLie n ds))
    (hP : RealLinkedStandardQuotientAnnihilatorStatement) :
    RealLinkedLanglandsQuotientNotLargeStatement := by
  intro n ds R hrank hord hlink _ hRtop hRmax hmf
  obtain ⟨W, hWgk, hWtop, u, huW, hu0⟩ := hP n ds hrank hord hlink
  exact hu0 (MaximallyFaithfulAnnihilator.envelopingAction_eq_zero (hZ n ds) hRtop hmf
    fun v => hRmax W hWgk hWtop (huW v))

end Langlands.Archimedean
