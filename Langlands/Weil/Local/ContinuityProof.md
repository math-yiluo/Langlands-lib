# Continuity and character inertia for the actual local Weil group

Author: Worker 106.

This module proves the existing `LocalWeilContinuityFor.{u,v}` and
`LocalCharacterInertiaFor.{u}` in `RepresentationStatements`, for every prime
`p` and actual field `F : PadicField.{u} p`. The representation carrier universe
`v` is independent of `u`; dimension zero is included.

`localInertia_nonarchimedean` restricts the open-subgroup neighborhood basis of
`localWeilGroup F` to actual inertia with its induced topology. Its proof adapts
the subgroup argument already implemented in `AssemblyProof`. The degree
kernel and inertia constructors are unchanged.

`localWeilContinuity` packages actual inertia as an open subgroup, equips it
with the compactness proved in `AssemblyProof`, and specializes the published
`representationContinuity` through `bundledRepresentationContinuity_iff`.
This supplies all five equivalences: operator continuity agrees with orbit
continuity, joint continuity, openness of the inertia kernel, and openness of
the whole-group kernel; an open inertia kernel is equivalent to finite inertia
image together with a closed inertia kernel. The bridge identifies the usual
complex carrier and endomorphism topologies, so no discrete coefficient
topology or additional witness enters the result.

`localCharacterInertia` attaches the scalar representation on `ℂ` to the given
continuous `ℂˣ`-valued character. Continuity of unit evaluation and complex
multiplication give orbit continuity and hence operator continuity. The
published nonarchimedean representation theorem gives an open kernel.
Evaluating scalar operators at `1` identifies that kernel with the character
kernel. Restriction gives an open kernel on actual inertia, and compactness
then gives finite image by `finite_range_of_open_kernel`.

These are internal specializations and a rank-one consequence of published
Library proofs, not new arithmetic assumptions. The source provenance is
inherited from `RepresentationStatements.md` and
`../Representation/ContinuityProof.md`: Henniart 1980, §2.1 and the opening of
§2.5, and Tate 1979, (2.1). The implemented specialization and scalar-kernel
argument are described above; no claim is made that either source states this
entire Lean conjunction verbatim.

The final two assignments check the complete unapplied theorem types against
the named existing propositions, including the field parameters and independent
carrier universe.
