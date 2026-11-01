# Leading Euler coefficients under finite flat pullback

`FiniteFlatPullbackEulerLeadingCoefficientStatement` concerns an actual smooth,
proper, geometrically connected scheme `X` of specified relative dimension `g`
over an arbitrary field `K`, an actual finite flat endomorphism `f` over `K`,
and an actual ample line bundle `L`. It compares any rational polynomials `P`
and `Q` that evaluate at every natural number, including zero, to the actual
Euler characteristics of the tensor powers of `L` and of `f* L`, respectively.
The cohomology finiteness proofs for both families are explicit inputs. The
Euler characteristic is the published integer alternating sum of dimensions
of actual derived relative cohomology, cast to the rationals.

The asserted equation is

```text
Q.leadingCoeff = (f.left.finrank x : rational) * P.leadingCoeff
```

at every target point `x`. The rank is Mathlib's native scheme-morphism rank,
computed from the actual finite algebra on affine charts. No numerical degree,
generic-rank certificate, or polarization identity is an input. The statement
makes no algebraic-closure, characteristic-zero, positive-dimension, or
nontrivial-polarization restriction. The dimension-zero case is included.

The supplied polynomials are required to represent the actual Euler functions;
they are not arbitrary numerical substitutes. Existence, the degree bound,
and ample positivity are the separate published statement
`SmoothProperLineBundleEulerPolynomialStatement`. This comparison does not
assume that statement as an outer proposition. Its hypotheses specify only
the two actual polynomial presentations needed to express the coefficient
equation. Finite-cohomology proof choices do not change the invariant.

This is a derived specialization of the registered Stacks Project source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`:

- In `0BEL.html`, Lemma 33.45.7 identifies the top intersection coefficient
  after pullback with the generic finite degree times the target coefficient.
  Lemma 33.45.11, also retained as `0BEX.html`, specializes this to an ample
  line bundle and a finite dominant map of proper varieties.
- Definition 33.45.10 and its following discussion identify the single-variable
  leading coefficient as the ample degree divided by `g!`. The same dimension
  occurs on both sides, so the factorial cancels.
- `02NY.html`, Definition 29.52.8, gives the generic field-degree convention.
  `02K9.html`, Definition 29.49.1 and Lemmas 29.49.2 and 29.49.5, supply the
  finite locally free rank convention. The native-rank identification is an
  obligation of this statement's proof, not an additional input equality.

The published `SmoothProperConnectedFiniteFlatGeometryStatement` and its proof
provide integrality, dimension `g`, surjectivity, and constant positive native
rank for this exact geometric situation. Thus the map is finite dominant and
both schemes are the same proper integral variety. At the generic point the
finite locally free rank is its generic algebra dimension, hence the finite
function-field degree used in the source. Finite pullback of an ample bundle
is ample. These facts and the source's ample degree comparison give the
asserted equality. There is no matching project errata note for this registered
source at preparation time.

This file states a remaining numerical-geometry prerequisite. It supplies no
proof of the comparison or of the host polarized finite-flat rank formula.
