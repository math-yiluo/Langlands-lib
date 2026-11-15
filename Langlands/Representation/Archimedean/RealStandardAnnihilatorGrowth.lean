import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.RealGenericLargeReduction
import Langlands.Algebra.UniversalEnvelopingFiltration

/-!
# Growth of the enveloping algebra acting on a real standard module

`RealStandardAnnihilatorGrowthStatement`: for every list `ds` of real blocks of total rank `n`,
the elements of degree at most `d` of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` act on the `O(n)`-finite functions of
the standard module of `ds` through a space of operators of dimension at least
`c (d + 1)^(n (n - 1))`, for some `c > 0` independent of `d`.

This is the lower half of a Gelfand–Kirillov dimension comparison: it says that
`U(𝔤) / Ann I(ds)` has Gelfand–Kirillov dimension at least `n (n - 1) = 2 dim 𝔫`.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

/-- **Growth of the annihilator quotient of a real standard module.** For every list `ds` of
real blocks of total rank `n` there is `c > 0` such that for every `d`, the image of the
degree-`≤ d` part `degreeFiltration ℂ (ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)) d` of the enveloping algebra under the
action `envelopingAction (realStandardLie n ds)` on the `O(n)`-finite functions of the standard
module has dimension at least `c (d + 1)^(n (n - 1))`. -/
def RealStandardAnnihilatorGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ,
    c * ((d : ℝ) + 1) ^ (n * (n - 1)) ≤
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
        (envelopingAction (realStandardLie n ds)).toLinearMap) : ℝ)

end Langlands.Archimedean
