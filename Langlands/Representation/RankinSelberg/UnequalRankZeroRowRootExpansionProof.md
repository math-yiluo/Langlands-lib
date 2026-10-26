# Uniform zero-row unequal-rank root expansions

`Langlands.RankinSelberg.unequalRankZeroRowRootExpansion.{uF,uV,uW} F T n k`
proves the published proposition
`UnequalRankZeroRowRootExpansionStatement.{uF,uV,uW} F T n k`.
The outer telescope retains the prime parameter and instance, the field `F`,
every supplied topological realization `T`, and every `n k : ℕ`. The three
universes are independent. The only expansion assumptions are the two
`CoefficientTorusExpansion` propositions already inside the target.

This is an internal derived proof of the adapter specified by the statement.
The original JPSS provenance and its scope are recorded in that statement's
paired Markdown. The implementation uses the current Library results described
below and elementary finite sums, rather than reproducing a source proof.
It establishes the pointwise root expansion; analytic assembly belongs to
the consumer of this statement.

## Coordinates and Schwartz factors

Write `A = Fin (n+1) → F.Carrierˣ` and
`d(a)_i = ∏_{j ≥ i} a_j`. The private `padOnes` function extends a finite
tuple by ones. `padOnesHom` is its multiplicative monoid map, and
`continuous_padOnes` proves continuity coordinate by coordinate.

`appendIdentity_diagonalUnits` uses the published `appendIdentity_entry`
formula to identify the actual matrix
`appendIdentity n (0+k+1) (Iwasawa.diagonalUnits b)` with the diagonal matrix
whose entries are `padOnes b`. Thus no unspecified embedding replaces the
larger-group argument.

`padded_root_coordinates` applies `rootCoordinateChange F T n` to verify
that the simple roots of this larger diagonal at `b = d(a)` are
`(a_0,…,a_n,1,…,1)`. It treats indices below `n`, the index `n`, and indices
above `n` separately. The same published coordinate theorem supplies the
smaller simple roots `(a_0,…,a_(n-1))`.

For larger and smaller Schwartz factors `φ` and `φ'`,
`paddedSchwartzProduct` constructs

```text
Ψ(x) = φ(padOnes x) · φ'(x_0,…,x_(n-1)).
```

Both factors are locally constant after their continuous pullbacks. Let `P`
be the projection from the larger root space onto its first `n+1`
coordinates. Then `P(padOnes x) = x`. If `Ψ(x) ≠ 0`, the point `padOnes x`
belongs to the support of `φ`, hence `x` belongs to the continuous image
under `P` of its compact closed support. This compact set contains the
support of `Ψ`, which proves compact support. This argument retains
`n = 0` and `k = 0`; it requires no compact-support assertion for the smaller
prefix pullback by itself.

## The fixed finite family and spectral shift

The two torus-expansion assumptions provide finite sets `X` and `Y` of
continuous functions with finite-dimensional left-translation spans. Set
`I = {χ // χ ∈ X} × {χ' // χ' ∈ Y}`. Put

```text
β       = -((0+k+1 : ℕ) : ℂ)/2,
c(a)    = ∏ j, (T.normalizedAbs(a_j) : ℂ)^((j+1)β),
η_(χ,χ')(a) = χ(padOnes(d(a))) · χ'(d(a)) · w(a) · c(a),
```

where `w` is exactly the inverse modulus in the target. The equivalent
parenthesization of `β` in Lean negates the entire quotient.

`rootPowerHom` constructs `c` as a complex-valued monoid homomorphism,
using multiplicativity of the normalized absolute value and the
multiplicativity of complex powers on nonnegative real bases.
`continuous_rootPowerHom` obtains continuity of the normalized absolute
value from `T.continuous_normalizedAbsHom`; on units the bases are strictly
positive, so complex exponentiation is continuous there.
`rootPowerHom_add` splits these products under addition of complex
exponents, using the nonvanishing of each base.

Apply `finiteFunctionClosure` to pull `χ` back along the padding monoid
map. Then `rootCoordinateFiniteFunction F T n` pulls the two finite
functions into cumulative-product coordinates and multiplies by the exact
inverse modulus `w`. Another application of `finiteFunctionClosure`
multiplies by the continuous character `c`. Consequently each `η` is
continuous and has the required finite-dimensional left-translation span.
The whole family depends on the representations' two finite expansion
sets and the fixed field, topology, ranks and shift. It is constructed
before both functionals, both coefficient vectors and the integral right
translate.

## Coefficient products and the closing identity

For given functionals `ℓ`, `ℓ'`, coefficient-model elements `f`, `f'`,
and `z` in the actual integral subgroup, apply the two expansion hypotheses
to

```text
modelRepresentation π ℓ (appendIdentity n (0+k+1) z.val) f,
modelRepresentation σ ℓ' z.val f'.
```

These elements stay in their original coefficient models. Their evaluations
are the original functions at the corresponding right translates. The
homomorphism law of `appendIdentity`, the actual diagonal-matrix identity,
and the root-coordinate identities give the two finite expansions at
`Iwasawa.diagonalUnits(d(a)) * z.val`.
Apply `paddedSchwartzProduct` to each pair of resulting Schwartz factors.
The resulting family is chosen before the root tuple `a` and complex
spectral parameter `s`.

The first clause of `rootSpectralWeight F T n` proves that the determinant
of `z` has normalized absolute value one. Its second clause identifies
the determinant weight at `s+β` with the corresponding product of complex
root powers. `rootPowerHom_add` then separates this into

```text
c(a) · ∏ j, (T.normalizedAbs(a_j) : ℂ)^((j+1)s).
```

Finally unfold the actual `unequalRankFunction` and use
`unequalRankMatrix_zero_rows`. These steps retain the determinant exponent
`s - ((0+k+1 : ℕ) : ℂ)/2` in the original function. Distribute the two
finite coefficient sums and regroup their factors by ring identities.
`Fintype.equivFin I` reindexes the product family as `Fin m`, with
`m = Fintype.card I`. Empty families therefore remain valid, as do zero
coefficients, zero functionals and zero representation spaces.

The proof adds no smoothness, Whittaker-type, nonzero, convergence,
rationality, common-denominator, Iwasawa, Mellin or spectral-shift
hypothesis. Its determinant-unit argument uses the target's integral
subgroup exactly.
