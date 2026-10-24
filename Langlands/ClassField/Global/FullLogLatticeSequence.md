# The exact sequence for adjoining integer constants

Let `F : Type u` be a field, let `E : Type v` be a number field with an
`F`-algebra structure, and write `G = E ≃ₐ[F] E`. The universes are independent.
No Galois or cyclicity assumption is needed here. All representations use the
existing scalar ring `k = NormalizedTwoCocycle.CoefficientScalars.{v}`, the
lifted integers, whose scalar action is through the underlying integer.

Write `M₀ = fullLogUnitLattice E` for the actual image of the weighted unit
logarithm, and `M = augmentedFullLogUnitLattice E` for the lattice obtained by
adjoining integer multiples of the all-ones vector. Both carry the restricted
arithmetic action on real infinite-place coordinates. The previously proved
`fullLogIntegralSplitRepresentationIso F E` identifies the representation on
`M` with that on `M₀ × k`, with trivial action on the second factor.

## Maps and short complex

`fullLogUnitProductInclusion F E` and `fullLogUnitProductProjection F E`
are morphisms of representations given by

\[
y \longmapsto (y,0), \qquad (y,z) \longmapsto z.
\]

Their intertwining equations follow directly from the product action.
`fullLogUnitAugmentedInclusion F E` composes the first map with the inverse
integral splitting. `fullLogIntegralConstantProjection F E` composes the
forward integral splitting with the second map. Thus their underlying maps are

\[
i(y)=\operatorname{split}^{-1}(y,0),\qquad
p(x)=\operatorname{split}(x)_2,
\]

where `split = fullLogIntegralSplitLifted E`. The two `_apply` lemmas in the
module give precisely these formulas. Through the imported construction,
`i` includes the unit logarithmic vector into `M`, and `p` extracts its unique
integral constant coefficient, lifted to `k`.

`fullLogLatticeSequence F E` is the short complex of these representations
and maps. Its zero-composite equation follows by applying the second
projection to `split (split⁻¹ (y,0)) = (y,0)`.

## Exactness and implemented proof

`fullLogLatticeSequence_shortExact F E` proves that this short complex is
short exact, giving

\[
0\longrightarrow M₀\xrightarrow{i}M\xrightarrow{p}k\longrightarrow0.
\]

The proof uses the existing `repShortExact_of_values` criterion from
`LocalUnitCohomology`. Injectivity of `i` follows from injectivity of
`split⁻¹`, followed by the first projection. If `p(x)=0`, the first coordinate
of `split(x)` is a preimage of `x` under `i`; the equality follows by applying
`split` and using the vanishing second coordinate. For any `z : k`, the
vector `split⁻¹(0,z)` maps to `z`, proving surjectivity. These elementwise
facts give categorical exactness, a monomorphism on the left and an
epimorphism on the right.

## Provenance and scope

This is a derived categorical adapter of Milne, *Class Field Theory*, v4.03
(2020), Chapter VII, proof of Proposition 3.1, printed p.209 (PDF page 218).
There the logarithmic image `M₀` lies in the coordinate-sum-zero hyperplane,
the all-ones vector is fixed, and `M = M₀ + ℤe` is used to adjoin a trivial
integer factor. Specializing the place set to all infinite places gives the
ordinary-unit setting used here. The concrete integral splitting and the
arithmetic representations have already been constructed in the imported
modules; this file packages their inclusion, projection and exactness.

The module does not prove multiplicativity of the Herbrand quotient,
cohomology finiteness, or the parent idele-class Herbrand quotient identity.
It supplies the exact sequence needed to apply such multiplicativity once
that separate cohomological result is available.
