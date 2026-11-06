# Finite local norm control in CM extensions

Author: Worker 1692.

This internal arithmetic helper supports the finite-local-norm compatibility
step in the proof of Harris–Taylor, Corollary VII.2.8, printed pp.244–245
(PDF pp.252–253). Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The constructions refine that argument to actual idele factors.

`completionUnitInclusion p q` is the continuous embedding of the groups of
nonzero elements for a finite completion extension. Its subspace topology
follows from the finite-dimensional closed embedding theorem, applied to the
base completion as a one-dimensional vector space over itself, and then the
subspace topology on the groups of units.

`exists_openSubgroup_norm_control` constructs an open subgroup in the extension
completion whose intersection with the embedded base consists of local norms.
The local norm image is a neighborhood of one in the base. The embedding
property realizes a smaller such neighborhood as the inverse image of an
ambient neighborhood. Van Dantzig supplies an open subgroup inside it.

In a quadratic extension a local degree is one or two. In the first case the
local norm is surjective, since the norm of an embedded base element is itself.
In the second case the local-degree sum forces there to be only one place
above the base place. Thus `ideleCoordinate_ideleNorm_mem_localNorm` shows
that the coordinate of an actual idele norm is a norm from any selected
completion above the given place.

`exists_placeAbove_not_mem` chooses a place outside `S` above every finite
place of the maximal real subfield. An arbitrary place above it suffices if
it is outside `S`; otherwise its conjugate is outside `S`, because `S` is
disjoint from its conjugate. Relative conjugation preserves the place below.
This avoids a separate splitting argument for places in `S`.

`exists_open_integral_subgroup_localNorm_control` constructs an open subgroup
`H` of the actual ideles of a CM field `K`. It is contained in the integral
ideles and contains every infinity idele. If a base idele `r` from the maximal
real subfield and an idele `s` whose finite coordinates outside `S` are one
satisfy `ideleInclusion r * s ∈ H`, then every finite coordinate of `r` is a
local norm from a completion of `K` above that place. No integrality or
infinity condition is imposed on `s` in this helper.

The subgroup intersects the integral ideles with the inverse images of the
local open subgroups constructed above, at the finitely many base places
with any ramification above them. For a chosen place outside `S`, the
coordinate of `s` is one. At a ramified place the open subgroup condition
therefore makes the base coordinate a norm. At every other place the integral
condition, the valuation formula for completion embeddings, and the
unramified unit norm theorem give a local norm witness. The finite
intersection remains open and contains infinity since every infinity idele
has finite coordinate one.

The module provides finite norm control. The sign calculation, compatibility
on the quotient kernel, and final Hecke-character construction are separate
steps.
