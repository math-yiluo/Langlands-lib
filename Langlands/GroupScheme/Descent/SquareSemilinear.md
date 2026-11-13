# Semilinear coherence for commuting pullback squares

This internal construction compares the two actual successive pullbacks of a
group scheme in a commuting square. Its inputs are arbitrary schemes in one
universe, four scheme maps, and the commuting equality.

`squareComparison` composes the published direct-pullback comparisons through
the same composite. Its projection formula and naturality follow from those
of `pullbackComparison`. `hom_ext_pullback_tower` proves that two homomorphisms
into an iterated pullback agree when their projections to the original group
agree, by cancelling the direct-pullback comparison and using pullback
extensionality.

`squareComparison_semilinear` assumes endomorphisms on the cover and the
upper corner that are compatible with the square. It compares canonical
semilinear transport through the two pullback routes. The proof reduces to
projection equality by the preceding extensionality result and applies the
published projection formula for `descentBaseChangeIso`.

These are internal coherence results for the published actual group-scheme
pullback APIs. They do not supply any datum, integer-ring cover, or descent
from stable integral points.
