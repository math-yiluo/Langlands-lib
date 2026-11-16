# Split Borel local conjugacy from structure and normalizer lifting

Worker 670.

This derived construction combines the two local Borel-conjugacy reductions.
Its final theorem has precisely the conditional type

`SplitBorelVectorSeriesStatement.{u} →
 SplitNormalizerGeometricLocalLiftingStatement.{u} →
 SplitBorelZariskiLocalConjugacyStatement.{u}`.

Both premises remain unproved inputs. This module does not give an
unconditional proof of the target.

For an arbitrary commutative ring `R`, a reductive `G` over `Spec R` and a
specified coordinate split torus homomorphism `t`, the first theorem assumes
`HasSplitBorelVectorSeries t` and any relative Borel subgroup `i : B → G`.
It concludes `HasZariskiLocalConjugateContaining t i`: at every point there
are an open neighbourhood `V` and an actual rational point `g` of `G_V`
such that the range of `t_V` is contained in the range of
`i_V ≫ (innerIso g).hom`, on every test scheme over `V`.

The proof unpacks the supplied Borel `B₀`, its inclusion `i₀`, its coordinate
torus quotient `q`, and the closed affine kernel `j` with its finite vector
series. Closedness of `j` supplies the monomorphism needed by descent.
The actual fppf quotient gives flatness, surjectivity, local finite
presentation and the equality between the actual kernel range and `range j`.
The factorization `t₀ ≫ i₀ = t` implies `range t ≤ range i₀` by factoring
each test-scheme point through `t₀`. The published containment reduction then
applies, since the quotient is the coordinate split torus. That reduction
already inverts the local conjugator to obtain the required orientation.
The retraction identity `t₀ ≫ q = 𝟙` is part of the supplied structural
predicate; this implication only needs the factorization, quotient and
kernel-series properties.

`splitBorelLocalConjugatorOfVectorSeries` chooses the open and rational point
from this existence result. Its sigma/subtype retains membership of the
given point in the open and the full subgroup-functor containment.

For the final theorem, introduce exactly the data and four split hypotheses
of the unchanged published target, with no extra hypothesis on the ring.
The supplied `SplitBorelVectorSeriesStatement` gives the structural predicate
for these data, and the first theorem gives part (1) for every relative Borel.
The published
`splitBorel_exists_open_normalizer_conjugacy_of_lifting` applied to the other
premise gives exactly part (2). Its conclusion uses an actual rational point
in the full normalizer of the pulled-back torus and equality of the
conjugated Borel ranges, rather than only a fibrewise comparison. The target
is therefore obtained by conjunction. This works for every universe and
every commutative ring, including disconnected and empty bases.

The provenance is internal derived content: this module only unpacks the
explicit structural predicate, factors actual points, applies the published
vector-series containment reduction and conditional normalizer-conjugacy
theorem, and chooses witnesses. It adds no original-source assertion.
Constructing the split Borel structure and proving geometric normalizer
lifting from the split data remain the two substantive prerequisites.
