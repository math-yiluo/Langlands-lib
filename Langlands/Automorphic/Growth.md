# Polynomial-growth rational adelic functions

For an actual number field `K : Type u` and any natural rank `n`, this module
constructs subspaces of the continuous complex-valued functions on
`GL_n(A_K)` invariant under left multiplication by `GL_n(K)`. The ambient
carrier is the published `ContinuousRationalFunctions K n`; the finite and
infinite adelic factors are the actual matrix groups over their adele rings.
All natural ranks, including zero, are allowed.

## Growth and the adelic action

`Langlands.Automorphic.HasPolynomialGrowth K n f` requires, for every
`b : FiniteAdelicGL K n`, polynomial growth of the infinite slice
`infiniteSlice K n b f`. Thus the quantifiers are

```
∀ b, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
  ∀ a, ‖f(a,b)‖ ≤ C * matrixHeight K n a ^ d.
```

The notation `f(a,b)` denotes evaluation on `AdelicGL.pair K n a b`.
The height is the concrete matrix/inverse height defined in the paired
`Langlands.Global.ArchimedeanGrowth` module. Both the constant and exponent
may depend on the finite argument `b`. No bound uniform over finite slices
is included.

`polynomialGrowthSubrepresentation K n` has as its underlying complex
submodule the intersection, over all finite slices, of the inverse images
of the archimedean polynomial-growth submodule. The theorem
`mem_polynomialGrowthSubrepresentation` identifies membership with exactly
the predicate above.

This subspace is preserved by the full adelic right action. If the translating
element has components `(g∞,gf)`, its slice at `b` is the right translate by
`g∞` of the original slice at `b * gf`. The proof uses
`AdelicGL.pair_mul_right` and the archimedean right-translation growth
estimate. It requires no bound on how the slice constants vary with `b`.

`PolynomialGrowthRationalFunctions K n` is the carrier of this actual
submodule. `polynomialGrowthRightAction` is the restricted complex-linear
representation. `polynomialGrowthInclusion` is its intertwining inclusion
into the ambient continuous right action, and its injectivity is proved.
`evaluate_polynomialGrowthRightAction` states the evaluation formula

```
(R(g) f)(x) = f(x * g).
```

## Smooth intersections

`smoothPolynomialGrowthSubrepresentation` intersects this space with the
published slice-wise smooth subrepresentation: real smoothness on every
infinite slice and local constancy on every finite slice, in addition to
ambient continuity.

`finiteSmoothPolynomialGrowthSubrepresentation` instead intersects with the
published space of real-smooth functions having a common open stabilizer
under finite adelic translation. These are subrepresentations of the full
adelic right action. The final theorem proves the inclusion of this stronger
space in the slice-wise smooth polynomial-growth space, using the existing
common-open-stabilizer inclusion.

## Source and construction boundary

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Corvallis Part I (1979), section 4.1, printed p.194 (one-based PDF p.189),
specifies the finite/infinite product and the smoothness convention.
Section 4.2(d), printed p.195 (PDF p.190), imposes slow increase separately
on every infinite slice at a fixed finite argument. The quantifier order
above follows that slice-dependent requirement. Section 1.2, printed
pp.189–190 (PDF pp.184–185), supplies the source notion of slow increase.

This contribution is derived infrastructure with an explicitly specified
matrix/inverse height. As explained in `Global/ArchimedeanGrowth.md`, comparison
with the source's Hilbert–Schmidt group norms has not been proved here.
Consequently this module does not claim an identification with source slow
increase or with the full automorphic space. Compact-finiteness, finiteness
under the enveloping-algebra center, and cuspidality are additional conditions.
The submodule intersections, translation preservation, faithful inclusion,
and evaluation formula are direct constructions on the existing functions;
there are no supplied growth-preservation or automorphic-existence axioms.

Registered source: `borel-jacquet-1979-automorphic`.
Original file:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256:
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
