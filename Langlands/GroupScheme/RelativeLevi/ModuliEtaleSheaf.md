# The etale sheaf of actual relative Levi images

This internal derived module packages effective descent of actual Levi images as
sheafness on the big etale slice. The base scheme and universe are arbitrary.
The hypotheses are a relative parabolic inclusion into a reductive group, a
supplied relative radical whose literal pullbacks are relative radicals under
all parameter base changes, and explicit restriction stability of Levi images.
The presheaf is exactly `moduliFunctorOfStability`: its values are actual subgroup
images on all relative tests and its maps are literal subgroup restriction
through the canonical direct/iterated pullback comparison.

For any etale cover of a parameter scheme, a compatible presheaf family gives
ordinary matching of subgroup images by forgetting the Levi-image certificates.
`matchingLeviSubgroup` constructs its descended subgroup, and
`isLeviImage_matchingLeviSubgroup` proves that this actual subgroup admits a Levi
presentation. The restriction recovery and equality detection theorems give the
existence and uniqueness required by `Presieve.IsSheafFor`.

Every covering sieve in the big etale slice contains an etale covering family.
Unique gluing on that family extends to the sieve: pull the covering family back
along an arbitrary sieve arrow and use local separatedness to compare the two
candidate restrictions. This yields full `Presieve.IsSheaf` on
`Scheme.etaleTopology.over S`, packaged as `moduliEtaleSheaf`. A surjective etale singleton is a covering family,
so the same theorem gives its singleton sheaf condition without restrictions on
the parameter source or target. Inclusion of the big Zariski topology in the big
etale topology then gives `Presheaf.IsSheaf` for the Zariski slice.

The provenance is the Library's actual-image cover descent and the general
presieve sheaf API. No global Levi or global section is supplied or chosen.
Radical base-change stability and Levi restriction stability remain explicit
premises in this module; their discharge for reductive parabolics is separate.
