# Multiplier comparison for actual fixed Harris frames

This internal unit derives the multiplier comparison from the existing actual
compatible frame, Weil functoriality and source form attaining one. The final
small-level rigidity proposition remains open.

`FormIso.multiplier_eq_of_intertwines` uses an actual compatible frame and an
intertwining equation between a target map that scales the target form by `c`
and a source similitude. If the source form attains one, the source multiplier
equals `c`. The proof evaluates the scaling law at frame images of a pair
where the source form is one, then cancels the frame's form-value trivialization.

`originalElement_multiplier_of_frame_isogeny` specializes this argument to the
actual rational Tate self-isogeny and actual Weil pairing. Its hypothesis is
the actual fixed-frame equation with an element of the original opposite Harris
group. Its conclusion identifies that element's multiplier with the diagonal
image of the rational polarization multiplier `q`. Rational Weil functoriality
supplies the target scaling law. The Harris source form attains one, and the
canonical scalar-extension equivalence preserves the original multiplier.
No compactness, positivity, finite-order or faithfulness assertion is used.

`OriginalLevelMultiplierFrameWitness` packages the actual frame, original
subgroup membership, frame equation and this multiplier equality.
`exists_multiplier_frame_of_levelIso_fixed` extracts the original witness
from an actual fixed level orbit using the existing extraction theorem and
adds the proved multiplier equality. All base and prerequisite hypotheses
are retained from the original actual level construction.

The claims are internal consequences of the imported definitions and proved
Weil functoriality; this unit makes no new external literature attribution.
Proving that the rational multiplier is positive and has unit valuation at
every finite place remains part of the full rigidity argument, as do finite
order and the passage from local identity to identity of the self-isogeny.
