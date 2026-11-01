# Local compactness and compact-open translation on actual adelic matrix groups

Author: Worker 2. Provenance: internal construction from the published actual
adelic matrix groups, the published proof of local compactness of number-field
adeles, and pinned Mathlib topology. No new original-literature identification
is made.

The field `F : Type uF` is any number field. Every natural matrix rank is
retained, including zero. The group carriers, finite restricted-product
topology, full product topology and units topologies are exactly those in
`AdelicGL`; no replacement topology or additional local compactness assumption
is introduced.

`FiniteAdelicGL.locallyCompactSpace` installs the published local compactness
proof for the actual finite adele ring. A finite matrix space is a finite
product of this ring and hence locally compact. Mathlib realizes its unit
group as a closed embedded subspace of the product of the monoid and its
opposite; this transfers local compactness to the actual finite adelic general
linear group. `AdelicGL.locallyCompactSpace` uses the same argument and the
published full-adele local compactness theorem.

The coefficient space `V : Type uV` has its own independent universe and is
any topological space. `AdelicGL.rightTranslate` sends a continuous function
`f` to the actual function `x ↦ f(x * g)`, using Mathlib's continuous right
multiplication map. Pointwise evaluation proves the identity and multiplication
laws; this convention gives a left group action on functions.

Local compactness of the actual full group makes evaluation jointly
continuous for the compact-open function topology. Composing that evaluation
with the continuous map `((g, f), x) ↦ (f, x * g)` proves continuity of the
uncurried translated function. Mathlib's compact-open currying criterion
then proves `continuous_rightTranslate`, in which the group element and
function vary simultaneously. Fixing the function proves continuity of every
orbit map. These arguments require no linear, norm, completeness or
finite-dimensional structure on `V`.

This unit makes no statement about derivative topologies, smooth orbit maps,
Haar normalization, nonzero induced sections, unitary completion or automorphic
existence.
