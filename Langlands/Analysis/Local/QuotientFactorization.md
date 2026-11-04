# Actual quotient charts from ordered factorization

This is a derived topological and measure comparison for the actual left
quotient `H \ G`, using the existing `LeftQuotient` carrier. Its application
is the ordered complementary-unipotent integration in Waldspurger (2003),
IV.1, printed p.279 (PDF p.45), and the composition assertion IV.1(12),
printed p.283 (PDF p.49).

Let `G` be a topological group, `H` any subgroup, `X` any topological space,
and `s : X → G`. Suppose a homeomorphism `m : H × X ≃ₜ G` satisfies the
literal formula `m(h,x) = h * s(x)`. The space `X` need not be a group.
In particular, this permits `X = V × W` and `s(v,w) = v * w` without a
commutativity or normality assumption.

`isHomeomorph_factorQuotient` proves that `x ↦ H * s(x)` is a
homeomorphism onto the actual quotient. Continuity follows by restricting
`m` to `(1,x)`. Equality of two cosets gives a subgroup element relating
their representatives; injectivity of `m` then identifies the second
coordinates. Surjectivity follows from that of `m`. Finally, the quotient
projection composed with `m` is the chart composed with the second
projection. The first composite is open, and the second projection is
continuous and surjective, which proves that the chart is open.

`factorQuotientHomeomorph` bundles this concrete map. Its application
formula is the actual coset formula, and its inverse on the coset of `g`
is the second coordinate of `m.symm g`.

For the measure comparison, assume that `G` is locally compact and Hausdorff
and `H` is closed. Supply Borel measurable structures on `G`, `H`, `X`
and the actual quotient, measures `μG`, `μH`, `μX`, and a compatible measure
`ν` on that quotient. The ambient measure is finite on compact sets; `μH`
is regular Haar measure and right invariant; `μX` is regular. Both factor
measures are S-finite. The key additional premise is the exact product
identity `MeasurePreserving m (μH.prod μX) μG`.

`IsCompatible.measurePreserving_factorQuotientHomeomorph` derives the
exact equation `Measure.map c μX = ν` for the concrete quotient chart
`c`, and its measurability. In particular, it retains the supplied
normalization rather than identifying measures only up to a scalar.

The implemented proof compares regular measures using real compactly
supported continuous quotient tests. The published
`realQuotientPositiveLifting` lifts each test `φ` to a compactly supported
continuous `f` on `G` whose subgroup integral is `φ`. Integrability of `f`
under `μG` and the supplied product identity give product integrability.
Scalar Fubini, with `H` integrated first, then identifies
`∫X φ(c(x))` with `∫G f`. Compatibility gives the same value for `∫ φ dν`.
Change of variables along the concrete chart and regular-measure
extensionality finish the proof. No product Borel-space assumption or
countability assumption is required: measurability and exact pushforward
for the product map are supplied by the displayed measure-preserving
premise.

The existence of these product factorizations for the required general
reductive subgroups, and their exact normalized Haar product comparison,
remain separate geometric and measure obligations. Applying this result
to ordered complementary root subgroups under the source's root-distance
condition must discharge both. The result does not establish the
root-distance composition theorem, convergence or continuation of standard
intertwiners, or Plancherel. In particular, the displayed product identity
is a premise of this derived comparison, not a permanent structural
assumption authorized for completion of the general program.
