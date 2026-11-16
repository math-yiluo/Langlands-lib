# Arbitrary base change inside a relative parabolic

This derived helper proves arbitrary base change for a supplied relative
unipotent radical, and hence for a supplied Levi subgroup, of a relative
parabolic in a reductive group scheme. The base and its change are arbitrary
schemes in the same universe. The conclusions use the actual pulled-back
homomorphisms.

It also constructs `RelativeLevi.moduliFunctorOfParabolic`, the presheaf on
the big slice whose values are the actual `LeviImage` subgroups. Its
restriction is precisely `restrictImage`, including the canonical comparison
from the iterated pullback to the direct pullback. No independent
restriction-stability assumption is required.

The source is Brian Conrad, *Reductive group schemes* (2014), the dynamic
description of parabolics in Corollary 5.2.7 and the discussion following
Definition 5.4.2, p.174; source identifier
`conrad-2014-reductive-group-schemes`. These are internal consequences of the
published relative dynamic and étale-local parabolic theorems, used in the
construction of the Levi moduli of Corollary 5.4.6.

In a dynamic presentation, uniqueness identifies the ambient image of the supplied
radical with the dynamic unipotent subgroup. Both the dynamic parabolic and
dynamic unipotent commute with arbitrary base change, so the dynamic
relative Levi theorem certifies the pulled-back radical.

For a general relative parabolic, choose an étale cover with dynamic
presentations and pull that cover back to the new base. Naturality of the
canonical comparison of iterated pullbacks identifies the two routes around
each square. Closedness, smoothness and normality are preserved directly
under base change. The geometric radical property at a point of the new base
is reflected from a point above it in this covering family. Finally, the Levi assertion follows by pulling
back its closed inclusion, smooth structure map, supplied radical and
Levi-times-radical multiplication isomorphism.

Restriction stability follows by taking a presentation of a Levi image,
pulling its homomorphism back and transporting its ambient group by the
canonical comparison. The existing restriction composition laws then supply
the presheaf laws.

The result concerns relative parabolics in reductive groups. It makes no
claim about arbitrary smooth ambient groups.
