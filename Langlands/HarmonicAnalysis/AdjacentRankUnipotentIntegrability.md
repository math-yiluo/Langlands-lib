# Convergence on rectangular upper-unipotent slices

This supporting module proves the compact-support and convergence facts used
by the two integrability conjuncts of
`Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement`.
These are internal topological consequences of the Library's actual matrix
and Schwartz–Bruhat definitions; they do not assert the Fourier equality.

For a Hausdorff topological field, any natural matrix size `n`, an actual
invertible matrix `g`, and a fixed column `y`, the map
`u ↦ rectangularJoin (g.val * u.val.val) y` from the actual upper-unipotent
group is a closed embedding. The implemented proof constructs a continuous
global retraction: take the rectangular matrix's first square block,
multiply it on the left by `g⁻¹`, extract its strictly upper entries, and
use the inverse of `GeneralLinear.upperEntryCoordinates` to reconstruct the
upper-unipotent element. Matrix inverse cancellation proves the retraction
identity. Mathlib's `Function.LeftInverse.isClosedEmbedding` then supplies
the closed embedding.

The definition `rectangularUnipotentSlice` packages the actual restriction
as a Schwartz–Bruhat function on the actual unipotent group. Local constancy
follows from continuity of the slice. The restriction
has compact support by `HasCompactSupport.comp_isClosedEmbedding`.
Multiplication by any continuous complex weight preserves compact support
and continuity. `Continuous.integrable_of_hasCompactSupport` proves Bochner
integrability against every supplied measure finite on compact sets. This
argument needs no comparison between actual group Haar and additive
coordinate products and no unitary norm estimate.

The theorem `adjacentRankUnipotent_integrable` specializes this result to
both displayed integrands of the published adjacent-rank statement. It
retains every natural `r`, including zero, the supplied character and
self-dual scalar measure, the actual sign and Weyl matrices, and the
published inverse-character partial and plus-character full Fourier
equivalences in their specified order. On the left it applies the slice
result with left matrix `1` to the partial Fourier transform of the ordinary
right translate. On the right it uses left matrix `weylLong (r+1) K` and
column `w*epsilon` for the full Fourier transform of the partial transform.
These transformed functions already belong to the Schwartz–Bruhat space
by the imported Fourier equivalences. The weights are continuous by
`Whittaker.inverseStandardCharacterContinuous` and
`Whittaker.standardCharacterContinuous`, composed with continuous inclusion
of complex units into complex numbers.

The Fourier specialization works over every Hausdorff locally compact
totally disconnected topological field carrying the given Borel structures,
and for every supplied unipotent measure finite on compacts. It therefore
applies directly to the statement's canonical p-adic field and actual
`RankinSelberg.unipotentHaar`, which is Haar and hence finite on compact
sets. It neither identifies that Haar with a coordinate product nor proves
the equality of the two integrals. The provenance of the specialization is
the convergence strengthening explained in the published
`AdjacentRankUnipotentFourierStatement` companion, for JPSS Section 6.2,
Lemma (2); all arguments implemented here are the elementary topological
consequences described above.
