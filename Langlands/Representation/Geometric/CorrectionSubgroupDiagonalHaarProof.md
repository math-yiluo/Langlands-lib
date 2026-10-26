# Actual diagonal Haar modulus on the full correction subgroup

Author: Worker 671.

`Langlands.Geometric.correctionSubgroupDiagonalHaar.{uF}` proves exactly the
published proposition
`Langlands.Geometric.CorrectionSubgroupDiagonalHaarStatement.{uF}`. Its import is
`Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof`.
The statement is preserved. The identical finite-product scaling helper is
shared with the block-modulus proof through
[FiniteProductMeasureScaling](../../HarmonicAnalysis/FiniteProductMeasureScaling.md).

The theorem retains every prime, every actual finite p-adic extension in the
arbitrary universe `uF`, every supplied topological realization `T`, every
natural rank, both arbitrary ordered block shapes, and every permutation. For

```text
H = U_B ∩ g⁻¹ P_C g,       g = permutation w,
A = { (a,b) | blockIndex B a < blockIndex B b
               and blockIndex C (w a) ≤ blockIndex C (w b) },
```

it identifies the actual `HaarModulus.closedNormalizerCharacter H hH d` with

```text
∏ (a,b) : A, T.normalizedAbsUnits (t a) / T.normalizedAbsUnits (t b).
```

Here `d` is a supplied element of the normalizer of the actual subgroup, and its
only extra premise is that its underlying matrix is literally the diagonal
matrix with entries `t i`. All topology, closedness, Haar existence and scaling
facts used below are constructed or obtained from published theorems within the
proof. Empty coordinate sets, including rank zero, are covered by the same
finite-product argument, with product equal to one.

## Coordinates and triangular left translation

Write `E = CorrectionEntry B C w`. The published
`correctionCoordinatesHomeomorph B C w R` is a homeomorphism from the inherited
subgroup `correctionSubgroup B C w R` to `E → R`; its maps are the published
`correctionCoordinates` and its inverse. The subgroup abbreviation is precisely
the intersection `H` above. The target-block condition in `E` is non-strict, so
these coordinates include the full correction subgroup.

The private lemma `correctionTranslation_depends` works over any commutative
ring `R : Type u`. For fixed `a` in that subgroup, define

```text
f(X) = coord(a * coord⁻¹(X)) - X.
```

Using `correctionCoordinates_mul_allowed`, its value at `(i,j)` is the constant
`coord(a)(i,j)` plus the sum of the terms
`coord(a)(i,k) * X(k,j)` over `CorrectionIntermediate B C w (i,j)`.
By `correctionIntermediate_gap`, every coordinate `(k,j)` in this sum has
strictly smaller `correctionGap` than `(i,j)`. Consequently two coordinate
functions agreeing at smaller gaps give the same value of `f` at `(i,j)`.
The lemma proves this by equality of finite sums and cancellation in the
additive group; it imposes no integral-domain hypothesis.

The public theorem `correctionCoordinateLeftTranslation_preserving` assumes a
topological commutative ring with continuous ring operations, a second countable
topology, and its Borel measurable space. For a family `μ : E → Measure R` of
sigma-finite additive-left-invariant measures, it proves that

```text
X ↦ coord(a * coord⁻¹(X))
```

preserves `Measure.pi μ`. The coordinate homeomorphism and continuous
multiplication make `f` continuous and hence measurable. The preceding
smaller-gap lemma gives the dependency condition of the published
`HarmonicAnalysis.finiteTriangularTranslation` theorem. Its transformation
`X ↦ f(X) + X` is exactly this left translation in coordinates.

## A Haar measure on the actual subgroup

The public theorem `correctionCoordinateHaar` adds a Borel measurable space on
the inherited subgroup and assumes that every `μ ab` is an additive Haar
measure, still sigma-finite. It proves

```text
ρ = (Measure.pi μ).map coord⁻¹
```

is an actual multiplicative Haar measure on that subgroup. The product measure
is finite on compact sets and positive on nonempty open sets. The inverse
coordinate homeomorphism transports both properties to the inherited subgroup.
For each `a`, the identity

```text
(a * ·) ∘ coord⁻¹ = coord⁻¹ ∘ (X ↦ coord(a * coord⁻¹(X)))
```

and the preceding measure-preservation theorem prove left invariance, using
composition of measurable pushforwards. This constructs Haar on `H` directly
from its coordinates.

In the final p-adic theorem the proof installs the topology and local-field
structure supplied by `T`, together with their proved separation, local
compactness, second countability and pseudometrizability facts. Closedness of
`H` is the statement's `General.isClosed_correctionSubgroup` proof, so `H` is
locally compact with its inherited topology. Its second countability and
pseudometrizability also follow from the coordinate homeomorphism. With the
Borel measurable spaces on the field and `H`, let every `μ ab` be `addHaar`.
These measures are sigma-finite additive Haar measures. The theorem above gives
`ρ.IsHaarMeasure`; the local compactness, second countability and
pseudometrizability instances supply `ρ.Regular` by the existing measure
regularity results. No additional topological choice is imposed on `T`.

## Diagonal conjugation and its pushforward scale

The public theorem `correctionCoordinates_diagonal_conj` works over any
topological commutative ring with continuous ring operations. For the supplied
literal diagonal equality, it proves

```text
coord(normalizerConj H d h)(a,b)
  = (↑(t a / t b) : R) * coord(h)(a,b).
```

First the product of the supplied diagonal matrix and the diagonal of the
inverse units is the identity; `Units.inv_eq_of_mul_eq_one_right` therefore
identifies the actual matrix inverse. Matrix multiplication by the two diagonal
matrices then computes the conjugated entry. The calculation uses inverses in
`Rˣ` and is valid without assuming that `R` is a field. The topological
hypotheses allow use of the actual continuous normalizer automorphism.

In the p-adic specialization put

```text
a_ab = t ab.1 / t ab.2,
c = ∏ ab : E, T.normalizedAbsUnits a_ab,
F(X)(ab) = (↑a_ab : F.Carrier) * X(ab).
```

The published `HarmonicAnalysis.padicScalarHaarScaling` theorem gives

```text
(μ ab).map (x ↦ ↑a_ab * x)
  = (T.normalizedAbsUnits a_ab : ℝ≥0)⁻¹ • μ ab.
```

`Measure.pi_map_pi` combines these equalities into the pushforward of the
product. The shared lemma `HarmonicAnalysis.pi_nnreal_smul` proves that the product
of nonnegative-real scalar multiples of sigma-finite measures is the product
of the scalars times the product measure; it uses equality on measurable
rectangles and the finite product of scalar actions. Product and inverse
identities in `ℝ≥0` then give

```text
(Measure.pi μ).map F = (c : ℝ≥0)⁻¹ • Measure.pi μ.
```

Let `α = HaarModulus.normalizerConj H d`. The diagonal coordinate lemma gives
`α ∘ coord⁻¹ = coord⁻¹ ∘ F`. Measurable pushforward composition and its
compatibility with scalar multiplication transport the product equality to

```text
ρ.map α = (c : ℝ≥0)⁻¹ • ρ.
```

## Identification of the actual character

The published `HaarModulus.normalizerCharacter_smul_map` applies to the regular
Haar measure `ρ` and states

```text
(normalizerCharacter H d : ℝ≥0) • ρ.map α = ρ.
```

Substituting the computed pushforward gives
`((normalizerCharacter H d : ℝ≥0) * (c : ℝ≥0)⁻¹) • ρ = ρ`.
To determine this scalar, the proof uses `haarScalarFactor_smul` and
`haarScalarFactor_self`: the Haar scalar factor of this scalar multiple
relative to `ρ` is the scalar itself, and the measure equality makes it one.
Since `c` is a positive unit, multiplication by its underlying value recovers
`(normalizerCharacter H d : ℝ≥0) = (c : ℝ≥0)`.

`Units.ext` gives equality in `ℝ≥0ˣ`, and
`HaarModulus.closedNormalizerCharacter_eq` identifies the statement's closed
wrapper with this character. Finally `map_div` rewrites each factor as
`T.normalizedAbsUnits (t a) / T.normalizedAbsUnits (t b)`; unfolding the allowed
entry subtype identifies its finite product with the statement's inline index.
Thus the claimed modulus is `c`, while conjugation pushes Haar forward by
`c⁻¹`, as required by the published convention.

## Provenance and scope

This is an internal derived analytic formula using the published actual
coordinates, finite triangular translation theorem, p-adic scalar Haar scaling
theorem, and actual normalizer Haar character. The direct imports are
`CorrectionSubgroupDiagonalHaarStatement`, `CorrectionSubgroupCoordinates`,
`TriangularTranslationProof`, `PadicScalarHaarScalingProof`, and
`FiniteProductMeasureScaling`, under their
respective Library namespaces. The proof supplies the measure construction,
triangular translation argument, conjugation calculation, finite product scaling
and character identification described above.

The original-source normalization and motivation are documented in the
[published statement's paired Markdown](CorrectionSubgroupDiagonalHaarStatement.md):
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 1.7 and 6.4, literature ID
`bernstein-zelevinsky-1977-induced-i`. This proof follows the coordinate measure
argument implemented here. It does not assert a separately quoted theorem of
that source or a correction-cancellation, orbit, or Jacquet-module comparison.
