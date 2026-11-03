# Integral actions on a supplied torsion-image quotient

This internal construction combines the exact scaled lifts in
`Langlands.CategoryTheory.RationalizationScaledActions`, the actual subgroup
in `Langlands.AbelianScheme.TorsionImageSum`, and actual isogeny factorization
in `Langlands.AbelianScheme.IsogenyActionDescent`. It proves the integral
ring laws and rational equivariance by two successive factorizations.
Its provenance is a deduction from these constructions; it introduces no
external geometric existence assertion.

Let `A` be an actual abelian scheme over an arbitrary scheme `S`, and let
`O` be a possibly noncommutative ring with a basis `b : Basis I ℤ O`, where
`I : Type u` has a `Fintype` instance in the universe of `S`. The ring may
be in a different universe. Let `α : O →+* Rationalization.End A` be the
original rational action, and let `s : ScaledIntegralLift α` be an exact
scaled integral lift. Write `n = s.denom` and `g(x) = s.map x`. This data
retains `n ≠ 0`, integer linearity of `g`, and the exact equations

- `ofEnd (g(x)) = n • α(x)`;
- `g(1) = n • 1`;
- `g(x) * g(y) = n • g(x*y)`.

These are integral scaled equations, not a claim that `g` is a unital ring
action. Endomorphism multiplication has the categorical convention
`f * h = h ≫ f`, so the third equation reads
`g(y) ≫ g(x) = [n] ≫ g(x*y)`.

Assume explicitly that the structure morphism of the actual torsion scheme
`A[n]` is finite and étale. `subgroup b s` is the actual finite étale
closed subgroup `K` obtained as the sum of the images of the restrictions
of `g(b i)` to `A[n]`. Supply `D : K.QuotientData`: its output abelian
scheme is denoted `B`, and its finite étale surjective quotient map is
`q : A → B`. The cartesian kernel square in `D` identifies the actual
scheme kernel of `q` with `K`. For the action construction also assume
`hn : IsIsogeny (n • 𝟙 A)`, meaning that multiplication by this signed
integer is finite, flat and surjective. These hypotheses and quotient
data remain inputs throughout this file.

`restriction_q_zero` proves that `g(x) ≫ q` kills `A[n]` for every `x`.
For a basis element this follows from the subgroup's component
factorization and the equation `K → A → B = 0`. For general `x`,
precomposition with the torsion inclusion and postcomposition with `q`
form an integer linear map on endomorphisms. Basis extensionality applied
to its composite with `s.map` extends the basis calculation.

`firstLift b s D hn x` is the actual homomorphism `h(x) : A → B`
obtained by factoring `g(x) ≫ q` through the isogeny `[n]`.
`firstLift_fac` gives `[n] ≫ h(x) = g(x) ≫ q`.
`map_comp_firstLift` proves
`g(y) ≫ h(x) = g(x*y) ≫ q`: cancel the isogeny `[n]`, commute integer
multiplication with `g(y)`, and use the exact scaled multiplication law.
For each basis element `y = b i`, restriction of this equation to `A[n]`
vanishes by `restriction_q_zero`. The subgroup's exact vanishing criterion
then proves `firstLift_kills_subgroup`: `h(x)` kills all of `K`.

`actionMap b s D hn x` factors `h(x)` through `q`, with the equation
`q ≫ actionMap x = h(x)` in `actionMap_fac`. The ring homomorphism
`action b s D hn : O →+* End B` bundles these maps. Unit, zero and
addition follow by cancelling `q` and `[n]` and using the corresponding
exact equations for `g`. Multiplication follows from
`g(y) ≫ h(x) = g(x*y) ≫ q` and the two factorization equations,
with the same endomorphism multiplication convention. No commutativity
of `O` is used.

`action_scaled_fac` records the exact integral intertwining equation

`[n] ≫ q ≫ action(x) = g(x) ≫ q`.

`action_unique` says that this equation determines the integral ring action
uniquely: cancel `[n]` and then `q` for every element of `O`.
`action_rational_fac` proves equivariance for the original rational action,

`ofHom(q) ≫ ofEnd(action(x)) = α(x) ≫ ofHom(q)`.

Its proof applies rationalization to the scaled equation, substitutes
`s.ofEnd_map`, and cancels multiplication by the nonzero rational integer
`n` in the rational Hom vector space. It does not assume injectivity of
integral Hom into rational Hom.

The inverse construction does not require `hn`. The subgroup inclusion
is killed by `[n]`, by `TorsionImageSum.inclusion_zsmul`. Consequently
`inverseMultiple b s D : B → A` factors `[n]` through `q`.
`q_inverseMultiple` gives `q ≫ inverseMultiple = [n]` on `A`.
Cancelling the quotient isogeny and commuting integer multiplication with
`q` proves `inverseMultiple_q`, the other composite equation on `B`.
`inverseData b s D` bundles these two actual maps and the same nonzero
integer. Its `rationalIso` is therefore an isomorphism from the
rationalization of `A` to that of `B`: its forward map is `ofHom(q)`,
and its inverse is `(n : ℚ)⁻¹ • ofHom(inverseMultiple)`.
`rationalIso_inv_fac` derives equivariance of this inverse from
`action_rational_fac` by cancelling the forward isomorphism.

All maps are actual homomorphisms of the given abelian schemes or their
specified rationalizations. The base may have nilpotents, the integer
may be negative, and the finite basis type may be empty; the stated
hypotheses still apply. Quotient existence, finite étale torsion and
isogeny hypotheses from characteristic zero, extension from an order to
its rational algebra, polarization transport, determinant and dimension
conditions, admissibility, and CM representability remain subsequent
obligations. No representing scheme or moduli comparison is asserted.
