# Compact real points and anisotropy

Author: Worker 263.

`Langlands.GroupScheme.HasCompactRealPoints G` means that the full real point
set of `G` is compact in the canonical regular-evaluation topology from
`AffinePointTopology`. Its carrier is
`G.affinePoints (CommAlgCat.of ℝ ℝ)`, so this is a property of the actual
scheme points, not of a supplied representation or a chosen topology.

The derived theorem `isAnisotropic_of_hasCompactRealPoints` proves that an
affine real group scheme with this property has split rank zero. No
smoothness, connectedness, reductivity or semisimplicity assumption is used.

The proof first shows that the real unit group is not compact. Compactness
would bound above the image of its continuous value map in ℝ, whereas the
positive unit with value `max b 0 + 1` exceeds any proposed upper bound `b`.
The published split-torus point homeomorphism identifies the real points
with a finite product of real unit groups. A coordinate projection is a
continuous surjection whenever the index type has an element, so a split
torus with compact points has empty index type. Finally, every closed split
subtorus of an affine real group induces a closed embedding on the actual
point spaces. Its points inherit compactness from the whole ambient point
set. The published characterization `isAnisotropic_iff` gives anisotropy.

Provenance: this is an internal derived real-field adaptation of the
published proof in `Rational.CompactPointsAnisotropy`, whose field
hypotheses are nonarchimedean. The scalar noncompactness argument here is
the order-boundedness argument for ℝ; the split-torus homeomorphism and the
closed-immersion comparison are imported from the published Library.
This unit does not assert that anisotropy implies compactness or construct
a real form.
