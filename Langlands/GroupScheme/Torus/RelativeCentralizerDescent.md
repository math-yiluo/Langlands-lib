# Smooth closed centralizers of relative tori over arbitrary bases

This internal support unit constructs a smooth closed representative of the
all-test centralizer of any homomorphism from a relative torus into a smooth,
relatively affine group scheme over an arbitrary base. The homomorphism need
not be an immersion.

The proof uses published smooth closed representability for split tori over
arbitrary rings. First, base changes of any subgroup satisfy all-test matching.
For a torus centralizer the subgroup descended from those base changes is the
original subgroup: commutation of points after any refinement is an equality of
morphisms, which can be checked on the pulled-back étale covering family.
Published closed-subgroup cover descent supplies a closed global representative.
Its pullbacks are isomorphic to the given smooth local representatives, so
smoothness descends along the same cover. An affine open cover gives the result
for a split torus over any scheme, and an étale splitting cover gives the result
for a relative torus.

The provenance is internal: the construction combines the published ring
centralizer theorem, effective epimorphic étale covers, closed subgroup descent,
and smoothness descent. This unit does not establish reductivity or maximality
of the resulting centralizer, or the full derived-group correspondence.
