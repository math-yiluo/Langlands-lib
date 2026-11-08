# Tadic's local reduction of the unitarizability of Speh representations

Module `Langlands.Representation.Classification.SpehUnitarizabilityReductionStatement`.

This module states, as proposition definitions, the local inputs of Tadic's
inductive proof that every Speh representation `u(δ, k)` of `GL_(k r)` over a
p-adic field is unitarizable, and the reduction itself as an implication. Nothing
is proved here. The reduction is the "trick of Tadic" (Tadic 1986, Lemma 6.2),
in the form of Badulescu 2014, Theorem 1(b). It avoids the global argument of
Tadic 1986, Theorem A.8.

Throughout, `F : PadicField p`, `T : F.TopologicalData`, the universes `uF`, `uV`
are independent, and all representations are actual smooth complex
representations `SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)`,
as in `SpehUnitarizabilityStatement`. A Speh datum `d` has rank `r = d.rank`,
length `k = d.length`, and block `δ = d.delta`; `d.degree = k * r`.
`d.IsDiscreteSeries` says that `δ` is irreducible, unitarizable and
square-integrable. `d.IsSpeh S` says that `S` is an irreducible quotient of the
centered product `ν^((k-1)/2) δ × … × ν^(-(k-1)/2) δ` and that every irreducible
quotient of it is isomorphic to `S` (`TadicUnitaryStatement`). So a
representation `S` with `d.IsSpeh S` is a representative of `u(δ, k)`.

## `SpehDatum.withLength`

`d.withLength k hk` is the Speh datum with the same rank `r` and the same block
`δ`, and length the positive integer `k`. It is a bookkeeping construction
(internal provenance). It is used to speak of `u(δ, k+1)` and `u(δ, k-1)`
together with `u(δ, k)`. Because the rank and the block are unchanged,
`(d.withLength k hk).IsDiscreteSeries` is definitionally `d.IsDiscreteSeries`.

## `SpehComplementaryIrreducibility`

For every datum `d` with `d.IsDiscreteSeries`, every `S` with `d.IsSpeh S`, and
every real `α` with `-1/2 < α < 1/2` and `α ≠ 0`, the actual complementary
product `d.complementaryInduced S α = ν^α S × ν^(-α) S` on `GL_(2 k r)` is
irreducible.

Source: Zelevinsky 1980, Proposition 8.5 (a product of irreducible
representations whose segments are pairwise not linked is irreducible) and
Proposition 8.6 (factorisation along straight lines `{ν^m ρ : m ∈ ℤ}` of the
cuspidal line). The support of `u(δ, k)` lies on one straight line. For
`0 < |α| < 1/2` the supports of `ν^α u(δ, k)` and `ν^(-α) u(δ, k)` lie on two
different lines, because `2α` is not an integer. So no segment of one factor is
linked to a segment of the other. Tadic 1986 uses this step in the proof of
Proposition 4.2 ("`σ^i_α × σ^i_{-α}` is irreducible for `α ∈ (-1/2, 1/2)`
since `σ^i` is supported in `ρ^ℤ` or `ρ^{1/2+ℤ}`"). Badulescu 2014,
Theorem 1(c) and its proof record the same irreducibility for
`α ∈ ]-1/2, 1/2[ \ {0}`.

The point `α = 0` is excluded on purpose. There, irreducibility of
`u(δ, k) × u(δ, k)` follows from Bernstein's theorem (Tadic 1986,
Theorem 2.5(i), the published `BernsteinUnitaryProductIrreducibility`) once
`u(δ, k)` is known to be unitarizable. This is how the reduction below uses it.

## `SpehNeighborProductIrreducibility`

For every datum `d` with `2 ≤ k` and `d.IsDiscreteSeries`, every `Sup` with
`(d.withLength (k+1) _).IsSpeh Sup`, and every `Sdown` with
`(d.withLength (k-1) _).IsSpeh Sdown`, the actual normalized product
`Sup × Sdown` is irreducible. In Lean this product is
`(T.binaryPositiveProductFunctor _ _).obj (Sup, Sdown)`, the published normalized
parabolic induction on the binary block shape `((k+1) r, (k-1) r)` of
`GL_((k+1) r + (k-1) r)`, with block `0` equal to `Sup` and block `1` equal to
`Sdown`.

Source: Badulescu 2014, Theorem 1(b), assertion (ii): "for all `k ≥ 2`,
`u(δ,k-1) × u(δ,k+1)` is irreducible", proved there with the
Moeglin–Waldspurger algorithm. The order of the two factors does not affect
irreducibility: by Zelevinsky 1980, Theorem 1.9, the two products have the same
composition factors. Lean uses the order `u(δ,k+1) × u(δ,k-1)` of the
end-point constituent below.

## `SpehNeighborProductEndpointSubquotient`

For every datum `d` with `2 ≤ k` and `d.IsDiscreteSeries`, and representatives
`S`, `Sup`, `Sdown` of `u(δ, k)`, `u(δ, k+1)`, `u(δ, k-1)` as above, the
following holds. If `Sup × Sdown` is irreducible, then it is a subquotient
(`SmoothRep.IsSubquotient`) of the end point
`d.complementaryInduced S (1/2) = ν^(1/2) S × ν^(-1/2) S` on `GL_(2 k r)`.
Before the comparison, the representation `Sup × Sdown` on
`GL_((k+1) r + (k-1) r)` is moved to `GL_(2 k r)` by the exact transport
`h ▸ _` along an equation `h : (k+1) r + (k-1) r = 2 (k r)`. The statement holds
for every such `h`; all such proofs are equal.

Source: Tadic 1986, Proposition A.4(ii): for multisegments `c, d ∈ M(D)`,
`L(c + d)` is a composition factor of `L(c) × L(d)`. Then Corollary A.6(i): if
`L(c) × L(d)` is irreducible, then `L(c) × L(d) = L(c + d)`. Apply this to
`c = ν^(1/2) a(δ, k)` and `d = ν^(-1/2) a(δ, k)`, the multisegments of
`ν^(1/2) u(δ, k)` and `ν^(-1/2) u(δ, k)` (definition of `u(δ, n)` before
Theorem A.8). Their sum `c + d` is `a(δ, k+1) + a(δ, k-1)`. Hence
`L(c + d) = L(a(δ, k+1)) × L(a(δ, k-1))` is `u(δ, k+1) × u(δ, k-1)` when this
product is irreducible (A.6(i) again). The same constituent is the one used in
the proof of Tadic 1986, Lemma 6.2. The hypothesis of irreducibility is the
form in which the reduction uses the result. It is supplied by
`SpehNeighborProductIrreducibility`.

## `SpehUnitarityInputs`

The conjunction of the three properties above, in the order
`SpehComplementaryIrreducibility ∧ SpehNeighborProductIrreducibility ∧
SpehNeighborProductEndpointSubquotient`.

## `SpehUnitarizabilityLocalReduction`

The implication

```
ComplementarySeriesUnitarity F T →
  BernsteinUnitaryProductIrreducibility F T →
    BernsteinUnitaryProductFactorUnitarity F T →
      SpehUnitarityInputs F T →
        SpehUnitarizability F T
```

with the same universes `uF`, `uV` throughout. The hypotheses are the published
Library statements of Tadic 1986, Proposition 2.9 (unitarity of the
complementary series and of the irreducible subquotients at its end point), of
Tadic 1986, Theorem 2.5(i) (Bernstein: products of irreducible unitarizable
representations are irreducible and unitarizable), and of the weak form of
Theorem 2.5(ii) used by Tadic (Hermitian factors of an irreducible unitarizable
product are unitarizable), together with the three Speh inputs. The conclusion
is exactly the published `SpehUnitarizability` (Tadic 1986, Theorem A.8): every
Speh representation of a discrete-series datum is unitarizable.

The Hermitian property of Speh representations, which the weak form of 2.5(ii)
needs, is not a hypothesis. It is proved separately, as the theorem
`SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh` of the module
`Langlands.Representation.Classification.SpehHermitian` (Tadic 1986,
Proposition 5.6(iii)).

Mathematical content of the reduction (Tadic 1986, Lemma 6.2; Badulescu 2014,
Theorem 1(b)), by induction on `k`. For `k = 1`, `u(δ, 1) = δ` is unitarizable.
For `k = 2`, the products `ν^α δ × ν^(-α) δ` are irreducible for `|α| < 1/2`. So
Proposition 2.9 makes the irreducible quotient `u(δ, 2)` of `ν^(1/2) δ × ν^(-1/2) δ`
unitarizable. For `k + 1` with `k ≥ 2`, the induction hypothesis and the inputs
make `ν^α u(δ,k) × ν^(-α) u(δ,k)` irreducible for `|α| < 1/2`. Proposition 2.9
then makes the irreducible subquotient `u(δ, k+1) × u(δ, k-1)` of the end point
unitarizable. The weak form of 2.5(ii) and the Hermitian property then make
`u(δ, k+1)` unitarizable.

## Provenance

Derived. The three inputs are source statements (Zelevinsky 1980, 8.5–8.6, as
used in Tadic 1986, 4.2; Badulescu 2014, Theorem 1(b)(ii); Tadic 1986, A.4(ii)
and A.6(i)), specialised to Speh representations and written with the Library's
actual objects. The following formulation choices are ours:

- the complementary interval excludes `α = 0`;
- the neighbour product uses the published binary product functor;
- the end-point statement is conditional on irreducibility;
- the rank transport to `GL_(2 k r)` is exact.

The reduction is the implication proved in Tadic 1986, Lemma 6.2, and
Badulescu 2014, Theorem 1(b), written with the published Library statements
as hypotheses.
