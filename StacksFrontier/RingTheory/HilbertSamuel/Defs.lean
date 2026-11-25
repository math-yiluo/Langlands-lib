module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The Hilbert–Samuel degree `d(M)` of a module

Let `(R, m)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition, that is an ideal
with `√I = m`, and let `M` be a finite `R`-module. The function
`χ_{I,M} : n ↦ length_R (M / I ^ (n + 1) M)` is a numerical polynomial; `d(M)` is its degree for
`I = m`, an element of `{-∞, 0, 1, 2, …} = WithBot ℕ`, equal to `-∞` exactly when `M = 0`.

## Main definitions

* `Ideal.hilbertSamuelDegree`: the degree of the numerical polynomial
  `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`, an element of `{-∞, 0, 1, 2, …}`, for an ideal
  `I ⊆ R` and an `R`-module `M`.
* `Module.hilbertSamuelDegree`: the invariant `d(M)`, that is `Ideal.hilbertSamuelDegree` for the
  maximal ideal of a local ring `R`.
* `IsIdealOfDefinition`: an ideal of a Noetherian local ring whose radical is the maximal ideal.
* `hilbertSamuel_chi`: the function `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`, valued in `ℕ∞`.

## Main results

* `chi_change_ideal_of_definition`: for ideals of definition `I, I'` and a finite `R`-module `M`
  there is `a > 0` with `χ_{I,M}(n) ≤ χ_{I',M}(a·n)` for all `n ≥ 1`.

## Tags

Hilbert–Samuel function, numerical polynomial, degree, Noetherian local ring, length
-/

@[expose] public section

@[expose] public section

open Filter IsLocalRing Polynomial

/-- The degree, an element of `{-∞, 0, 1, 2, …} = WithBot ℕ`, of the numerical polynomial
`χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`: the degree of a polynomial `P ∈ ℚ[t]` with
`P(n) = χ_{I,M}(n)` for all `n ≫ 0`, and `-∞` if there is no such polynomial. -/
@[stacks 00KA "Definition 00KA is the case `I = maximalIdeal R`, spelled
`Module.hilbertSamuelDegree`. The definition is stated for an arbitrary ideal because that is the
generality of the surrounding section, and because Lemma 00K9(2) is the assertion that this value
is the same for all ideals of definition."]
public noncomputable def Ideal.hilbertSamuelDegree {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] : WithBot ℕ :=
  open Classical in
  (if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        P.eval (n : ℚ) = (p : ℚ) then h.choose else 0).degree

/-- The invariant `d(M) ∈ {-∞, 0, 1, 2, …} = WithBot ℕ` of a module `M` over a local ring
`(R, m)`: the degree of the numerical polynomial `χ_M(n) = length_R (M / m ^ (n + 1) M)`, that is
`Ideal.hilbertSamuelDegree` at the maximal ideal. -/
@[stacks 00KA "The `d(M)` of the definition. Case (1) is not a separate branch: for `M = 0` the
polynomial computing `χ_M` is `0`, whose degree is `-∞ = ⊥`, and conversely a computing
polynomial of degree `-∞` forces `M = m ^ n M` for `n ≫ 0`, hence `M = 0` by Nakayama. See the
module docstring."]
public noncomputable abbrev Module.hilbertSamuelDegree (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : WithBot ℕ :=
  (maximalIdeal R).hilbertSamuelDegree M

end

end

/-!
## Changing the ideal of definition
-/

@[expose] public section

end

@[expose] public section

end
