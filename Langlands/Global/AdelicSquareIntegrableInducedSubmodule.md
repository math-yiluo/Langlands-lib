# The complex submodule of square-integrable adelic inducing forms

`Langlands.Global.AdelicGroupPoints.squareIntegrableInducedForms` realizes the
Library's `IsSquareIntegrableInducedForm` predicate as a complex submodule of
`G(𝔸_F) → ℂ`, with the same parabolic, Levi, radical, compact subgroup, and
automorphy data. `mem_squareIntegrableInducedForms` is the definitional
membership equivalence. The submodule neither takes a closure nor passes to
almost-everywhere classes of the inducing forms.

## Implemented construction

Let `[M] = A_M M(F) \ M(𝔸_F)` be the canonical split-centre quotient of the
Levi. The proof uses a private linear map on scalar functions, with value at
`(k, q) ∈ K × [M]` given by

\[
  T(\phi)(k,q) = m^{-\rho_P}\,\phi(mk),\qquad m=q.\mathrm{out}.
\]

Here the power uses the image of `m` under the Levi embedding, and the
argument `mk` uses the image in `G(𝔸_F)`. The map is defined using the chosen
representatives. For a continuous, left-invariant, split-component-equivariant
form, the expression on `K × M(𝔸_F)` is invariant under left multiplication
in the second variable by `A_M`: the factor `a^{-ρ_P}` cancels the factor
`a^{ρ_P}` from the form. For `M(F)` the form is invariant and the parameter
power does not change, since rational points lie in `M(𝔸_F)^1`. Invariance
under the join of the two subgroups gives continuous descent to `K × [M]`
using `LeftCosetSpace.continuous_out_of_invariant`. No continuity or
measurability of the representative selector is assumed. Open sets of `[M]`
are measurable because their inverse images in `M(𝔸_F)` are open and the
quotient sigma algebra tests measurability by those inverse images. Second
countability then makes open sets of the product measurable for the product
sigma algebra.

The norm square of `T(φ)` is pointwise the weighted square in
`IsSquareIntegrableInducedForm`, since `(-ρ_P) + (-ρ_P) = -2ρ_P` and the
power and the complex norm are multiplicative. With the product of compact
Haar probability on `K` and the canonical measure on `[M]`, the proof
therefore uses `memLp_two_iff_integrable_sq_norm` in both directions. The
linear map and the `MemLp` closure lemmas give the integrability clause for
sums and scalar multiples. The automorphy clauses use the existing
`automorphicFunctionsOn` submodule, and the split-component law remains true
by linearity of evaluation. All three clauses hold for the zero form.

## Provenance and use

This is an internal construction on the weighted realization of `A²_P`
from `AdelicSquareIntegrableInducedForms`, which follows E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series* (2011), §2, p. 311 (registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`). That passage
imposes the half-modulus law on `A_M` and square integrability modulo `A_M`.
The normalization above proves the submodule laws for the Library's exact
predicate without additional measure-compatibility hypotheses.

In a finite-dimensional span of intertwining outputs already known to be
square-integrable inducing forms, basis vectors from that span satisfy the
same predicate by submodule closure. This file does not prove that the
intertwining outputs lie in `A²_Q`, that they have finite-dimensional span,
or that their continuation is holomorphic on the imaginary axis.
