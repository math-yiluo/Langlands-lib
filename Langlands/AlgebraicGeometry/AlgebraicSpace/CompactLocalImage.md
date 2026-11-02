# Compact representations of local chart images

This derived helper isolates the compact union step in the registered Stacks
Project Lemma 67.50.1 (Tag 03XW), `03XW.html:209-215`. It uses the actual open
gluing in `OpenChartUnion`. The universe and the scheme base are arbitrary.

`HasCompactRepresentation A` means that an actual scheme over the fixed base
represents the subfunctor `A` and has a compact underlying space. Compactness
here is ordinary quasi-compactness and includes no Hausdorff assumption.

`localClosure_mono` proves monotonicity of local closure directly from covering
sieves. For a sheaf ambient presheaf, `sheafify_sup_sheafify` proves that locally
closing one summand before taking the local union does not change the result.
It uses monotonicity and idempotence of local closure.

`of_open_chart` shows that a represented open chart with compact source already
represents its local image. Its range is closed under fppf-local membership by the published
covering-sieve criterion for open subfunctors. The monomorphic chart
is isomorphic to its range, giving the stated representation.

`of_union` assumes an open chart with compact source and an etale chart whose
local image has a compact representation. The representation of that image,
followed by its open inclusion, gives a second represented open chart. The
two charts glue through `OpenChartUnion`; its finite open cover proves
compactness. Computing the two ranges and using the local-closure identity
identifies this actual gluing with the requested local union.

The helper does not assume or prove effective descent or representation of the
ambient presheaf. In particular it leaves the final schemehood theorem open.
