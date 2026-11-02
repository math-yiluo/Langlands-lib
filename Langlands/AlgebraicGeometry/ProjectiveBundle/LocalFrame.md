# Coordinates of genuine local frames

A `LocalFrame M n U` is an actual isomorphism from the free structure-module
sheaf on `n + 1` generators to `M` on the slice site of opens contained in
`U`. It gives a linear coordinate equivalence for the sections of `M` on
every smaller open, with inverse given by the finite basis expansion.
The construction uses the existing local basis sections and coordinate
functionals. The inverse sends a standard coordinate vector to the
corresponding basis section.

These equivalences commute with restriction of sections and coefficients.
Frames themselves restrict to arbitrary smaller opens using the slice-site
restriction functor and its comparison for free sheaves. The dual frame is
the existing actual dual free-sheaf isomorphism; its generators are the
coordinate functionals of the original frame.

`LocalFrame.change` changes coordinates from one frame to another on a
common smaller open. It is the inverse of the first coordinate equivalence
followed by the second. Identity and composition follow by cancellation.
Applying a structure-sheaf restriction to its matrix entries gives exactly
the change on the smaller open, proved by naturality of the coordinate
functionals and compatible basis sections.

This is derived internal infrastructure, using `ModuleDualLocalFree` and
the existing coefficient-change construction. It makes no external source
assertion. When the frames are duals of frames of `M`, their coordinates
are evaluations on the original basis, which is the convention needed for
rank-one quotients of `M`. A projective bundle, comparison between covers
and a representing moduli scheme are not constructed in this file.
