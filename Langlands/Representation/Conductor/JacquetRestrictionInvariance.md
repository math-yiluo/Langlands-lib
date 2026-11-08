# From Levi restrictions to Jacquet invariance

This internal auxiliary works with the actual standard-character Whittaker
functions on `GL_(n+2)(F)`, their corank-one Levi restriction and the actual
mirabolic subgroup. The field and representation carrier have independent
universes. The basic calculations assume a field with a topology and a bundled
unitary additive character, without local compactness, smoothness, admissibility
or irreducibility. All `n : ℕ`, including `n = 0`, are allowed.

## Values and equality on the mirabolic

Write a mirabolic matrix as
`p = [[A,v],[0,1]]`, with `A` in `GL_(n+1)(F)` and `v` a column of length `n+1`.
The published `Mirabolic.eq_radicalElement_mul_levi` factors it as
`[[1,v],[0,1]] * diag(A,1)`. The standard Whittaker character of the radical
factor is `ψ(v_last)`: among the superdiagonal entries, only its final entry
can be nonzero. The private `standardCharacter_radical` proves this by splitting
the finite superdiagonal sum into its final term and the other zero terms.

`whittaker_mirabolic_value` applies Whittaker equivariance to this factorization
and proves

`W(p) = ψ(v_last) * W(diag(A,1))`.

Here the scalar character is the complex value `ψ.complex`.
`whittaker_mirabolic_eq_of_levi_eq` consequently proves equality on every
mirabolic element from equality on every corank-one Levi element. This is a
calculation within the mirabolic; it does not prove equality on the full group.

## Integral support and right invariance within the mirabolic

For any subring `O` of `F`, `HasIntegralLastRowSupport ψ O W` means that, whenever
`W(diag(A,1))` is nonzero, every entry of the last row of `A` belongs to `O`.
This is a supplied support condition, not a conclusion about all Whittaker
functions or essential vectors.

`right_jacquet_on_mirabolic_of_integral_support` assumes this support condition,
triviality of `ψ` on `O`, and right `GL_(n+1)(O)` invariance of the Levi
restriction. It proves `W(p*h) = W(p)` for every mirabolic `p` and every `h` in
the actual `fieldJacquetMirabolic O (n+1)`. This group is the intersection of the
integral subgroup with the mirabolic. Its integral subgroup requires integral
entries for both a matrix and its inverse.

The private `projection_mem_integral` checks both sets of entries in the
upper-left block, so the projection of `h` is an allowed integral Levi factor.
The projected product is `A*B`, and right Levi invariance removes `B`.
If the remaining Levi value vanishes, both sides vanish. Otherwise the new
radical phase differs by `ψ((A*u)_last)`, where `u` is the integral last column
of `h`. Integral last-row support makes this coordinate a finite sum of
products in `O`. The character is trivial there, so the extra phase is one.
The proof uses the published `lastColumn_mul` formula and closure of a subring
under finite sums and multiplication.

## Lifting through supplied restriction injectivity

For an actual representation `π` on `V` and a standard Whittaker functional `ℓ`,
`modelMirabolicRestriction` is the complex linear map from the actual
`coefficientModel π ℓ` to functions on the actual mirabolic, given by evaluation.
No replacement model or substitute action is introduced.

`modelMirabolicRestriction_injective_of_carrier` assumes injectivity of

`v ↦ (p ↦ ℓ(π(p)v))`

on the original carrier `V`, and transfers it to this coefficient image.
Surjectivity of the published `modelMap` supplies original-carrier preimages;
injectivity makes those preimages equal, hence makes their model images equal.
The theorem does not establish the supplied injectivity hypothesis.

`mem_fixedVectors_of_levi_restriction` assumes that the model restriction map
is injective. For any subgroup `H` of the full group, equality of `w(g*h)` and
`w(g)` for all Levi elements `g` and all `h` in `H` then implies membership in
the actual `fixedVectors (modelRepresentation π ℓ) H`. The proof compares `w`
with its actual right translate, proves equality on the mirabolic from the
Levi calculation, and applies the supplied restriction injectivity.

`mem_jacquetFixedVectors_of_integral_support` combines this lifting with the
integral support calculation to obtain global `H(0)` fixedness in the
unchanged coefficient model. The final
`mem_jacquetFixedVectors_of_integral_restriction` specializes `O` to the actual
valuation integer subring. Its Levi hypothesis is exactly the published
`IsIntegralInvariantOnRestriction π ℓ w`, the restriction predicate appearing
in `IsEssentialVector`. It retains integral last-row support, character
triviality and mirabolic restriction injectivity explicitly.

## Provenance and remaining obligations

The unit has internal provenance: its new conclusions follow from the published
mirabolic decomposition and multiplication formulas, standard-character
equivariance, subring closure and the actual coefficient-model action. No new
source-attributed analytic assertion is used.

In particular, the unit does not derive support from the essential identity or
prove arbitrary-field mirabolic restriction injectivity. It also does not
construct an essential vector, derive the scaled opposite invariance, compare
local factors or prove a minimal level or its dimension. It supplies a concrete
conditional step toward the conductor argument; it does not prove
`EssentialConductorStatement`.
