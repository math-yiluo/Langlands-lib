# Gluing matching local opposite Borel subgroups

This module uses the Borel transport lemmas of `BorelEtaleTransport`.

This internal auxiliary lemma assembles a global opposite Borel once compatible
local opposite Borels have been supplied. Its base is an arbitrary scheme and
the ambient group scheme is affine over that base. It assumes a small étale
cover, actual closed relative Borel inclusions on its members, their all-test
matching condition, and equality of each local intersection with the supplied
closed subgroup. That subgroup is also assumed contained in the original
global subgroup. Neither local existence nor matching is proved here.

The universal descended subgroup is closed representable by `EtaleDescent`.
Its base changes have the supplied local ranges. The representing inclusions
are therefore isomorphic compatibly with their maps to the ambient group.
The local Borel predicates transport through these isomorphisms and descend
by `IsRelativeBorelSubgroup.of_etale_cover`.

For the intersection, containment in the supplied closed subgroup is detected
on the étale cover by `le_range_iff_baseChange_etaleCover`. The local
intersection equalities prove this containment. They also show that the
supplied subgroup is contained in the descended Borel. Together with its
assumed containment in the original subgroup, this proves the reverse
inclusion. All equalities concern subgroup functors on arbitrary test schemes.

This is a derived implementation of the descent step used in Conrad,
*Reductive group schemes* (2014), Proposition 5.2.12, p.158.
