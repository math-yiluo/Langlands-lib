# Arithmetic transport on actual adelic general linear groups

Author: Worker 2.

This internal construction applies the published arithmetic ring equivalences
to every entry of a matrix unit and its inverse. The number fields `K`, `L`
and `M` have independent universes. The rank `n` is any natural number,
including zero. No topology on the rational field points is selected.

`adelicEquiv`, `finiteEquiv` and `infiniteEquiv` are continuous multiplicative
equivalences between the existing full, finite and infinite adelic GL groups.
Their inverse maps apply the inverse arithmetic ring equivalence entrywise.
The matrix-unit inverse identities follow entrywise from the ring inverse
identities. Continuity uses the existing units topology and Mathlib's
continuous map on general linear groups. The identity and composition laws
follow from those of arithmetic transport on adeles.

`localEquiv` is the corresponding continuous multiplicative equivalence
between the actual finite completion at the pulled-back place and the
completion at the target place. The entrywise formulas expose the actual
ring and completion maps. Finite local projection commutes with transport.
Integrality of a local matrix and its inverse is preserved and reflected
using the proved valuation-subring correspondence. Surjectivity of the
place equivalence then proves preservation and reflection of membership
in the full standard integral finite adelic subgroup.

The rational matrix compatibility formula uses the original field
isomorphism on rational entries. The full finite and infinite projections,
pairing of the two factors, and insertion of either whole factor commute
with transport. Determinants commute with the actual idele equivalence,
and scalar matrices transform by that same idele equivalence.

`adelicAut` is the monoid homomorphism from actual rational field
automorphisms to automorphisms of the full adelic GL group. It acts
covariantly, by applying the field automorphism to the arithmetic adele
entries. `adelicAction` bundles the installable multiplicative left action;
it installs no global action instance.

The three CM specialization lemmas identify the general equivalences with
the existing `CMConjugation.adelicConj`, `finiteConj` and `infiniteConj`.
They compare the actual entrywise maps, and do not alter those definitions.
No assertion about differentials, automorphic analytic conditions or
representation occurrence is made.

Provenance is internal composition of the published arithmetic
adele/completion equivalences with the existing matrix-unit groups,
local projections, integral subgroups, factor decomposition, determinant
and scalar maps. It introduces no new identification with literature.
