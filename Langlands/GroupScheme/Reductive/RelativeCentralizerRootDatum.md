# Full coordinate root data for relative cocharacter centralizers

This derived module proves that the full coordinate root datum of an actual
relative cocharacter centralizer is the orthogonal restriction of the supplied
ambient datum. Both entire character and cocharacter lattices are retained;
only the root and coroot index set is restricted. The orthogonal pairing is the
existing `Langlands.LinearAlgebra.orthogonalRootPairing`.

The field theorem `IsRootDatumOf.coordinateCentralizer` starts with the actual
field realization of a coordinate root datum and a supplied closed representative
of the cocharacter centralizer, with the original torus factored through it. It
proves that the field realization of the coordinate orthogonal restriction is
the actual root datum of that factored torus. The roots are exactly the ambient
roots pairing to zero. For each such root, the ambient reflecting normalizer fixes
the cocharacter, so its actual point factors through the represented centralizer.
This realizes the same reflection in that centralizer. The pairing is unchanged.
This is the coordinate version of the published orthogonal-root-pairing proof,
with the actual field realization checked directly.

The relative theorem `IsFibrewiseRootDatumOf.coordinateCentralizer` assumes an
affine group of locally finite presentation over an arbitrary commutative ring
and a supplied finite reduced full fibrewise coordinate root datum. The actual
relative centralizer is `splitTorus.RelativeCocharacterCentralizer.groupScheme`,
with its actual inclusion and torus homomorphism. After each supplied field-valued
base change, that inclusion represents the centralizer of the same fixed integer
cocharacter, and the torus square commutes. The field theorem therefore supplies
each required actual root-datum certificate. Finiteness and reducedness pass to
the orthogonal root indices.

`centralizerRootDatumData` packages the explicit restricted datum together with
this actual fibrewise certificate. No localness, reducedness, connectedness or
nonzero-ring assumption on the original coefficient ring is used, and the proof
does not require reductivity beyond what a caller may use to supply the stated
hypotheses.

The result supports comparison of cocharacter centralizers in Task 7200. It does
not by itself prove parabolic equality, canonical filtration overlap compatibility
or the final descent theorem.
