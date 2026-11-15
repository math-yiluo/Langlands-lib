import Langlands.Global.RankinSelberg.ProjectionExpansion

/-! # The Whittaker expansion of the dual cusp forms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

namespace Unfolding

local instance dualWhittakerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualWhittakerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The Whittaker expansion of the dual cusp forms of an actual cuspidal realization: for every
standard additive character `ψ` and vector `v`, the dual function `φ̃ = dualFunction φ`
(`φ̃(g) = φ(w ᵗg⁻¹)`) is the sum over `N_r(F) \ GL_r(F)` of `W̃(diag(γ, 1) g)`, where
`W̃ = dualFunction W` is the dual of the `ψ`-Whittaker function `W` of `φ`. The sum converges
absolutely, and the partial sums of the absolute values converge uniformly on compact sets. -/
def DualCuspidalWhittakerExpansion {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r) :
    Prop :=
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ → ∀ v : T.Space,
    (∀ g : Points F (r + 1),
      Summable (fun q : UnipotentRationalCosets F r =>
          ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g)‖) ∧
        HasSum (fun q : UnipotentRationalCosets F r =>
          dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g))
          (dualFunction F (r + 1) (cuspFunction F T v) g)) ∧
    ∀ C : Set (Points F (r + 1)), IsCompact C →
      TendstoUniformlyOn (fun (s : Finset (UnipotentRationalCosets F r)) g =>
          ∑ q ∈ s, ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v)
            (cornerAdelicPoint F r q.out * g)‖)
        (fun g => ∑' q : UnipotentRationalCosets F r, ‖dualFunction F (r + 1)
            (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g)‖) atTop C

end Unfolding

/-- Every vector of every actual positive-rank cuspidal realization has the Whittaker expansion
of its dual cusp form, with absolute convergence that is uniform on compact sets (Cogdell 2004,
Theorem 1.1, applied to the contragredient cusp form `φ̃` and the character `ψ⁻¹`). -/
def DualCuspidalWhittakerExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r), DualCuspidalWhittakerExpansion F T

end Langlands.Global.RankinSelbergGlobal
