# Actual centralizer valuation and full V6 under field restriction

This internal construction compares the actual centralizer valuations for
integer-valued valuations on a field and an extension field, both in an
arbitrary universe. The original
acting torus is split, and its upstairs torus and centralizer source are
literal scheme base changes. The scalar orders agree exactly on original
field units. Bijectivity of the character restriction-evaluation maps is
supplied both downstairs and upstairs; no preservation of that algebraic
property across arbitrary extensions is asserted.

The positive centralizer valuation at an extended original rational point
is the actual real cocharacter base change of its original valuation.
To prove this, pull the upstairs vector back through the split cocharacter
equivalence and test it against every original rational character of the
centralizer. Character restriction and character evaluation commute with
base change, so the exact scalar-order identity gives the original
normalization. Injectivity of the original restriction-evaluation map
identifies the vectors. The proof does not assume that all upstairs
centralizer characters descend. Negating this identity gives the same
comparison for KP's negative translation.

`IsCentralizerCompatible.fieldRestrict` descends full V6, for every original
relative root, every original rational point of the centralizer source,
and every original root-group point. Here the original group is affine and
locally of finite type. The root functions downstairs are literally the
upstairs functions evaluated on the base-changed character and the scalar
extension of the original point. Actual root membership and root-group
points extend. Scalar extension commutes with the homomorphism from the
centralizer source to the group, multiplication, and inversion, so upstairs
V6 gives the downstairs conjugation formula. The proved negative
translation comparison and cocharacter evaluation identity identify its
real translation term. No root-valuation axioms or assertion that the source
represents the centralizer are needed for this family-level implication.

`fieldRestrictApartment` assumes a smooth affine original group, a
monomorphic inclusion of the split torus, and the original opposite factor
pairs. It also assumes the integer valuation order is nonzero at some
original field unit and a supplied upstairs apartment with the upstairs
integer valuation order. Casting that order to a real unit homomorphism
allows the full existing apartment restriction construction to be applied.
Exact order restriction then gives precisely the original integer valuation
order downstairs. The carrier remains the literal restriction image of the
upstairs carrier, as `fieldRestrictApartment_carrier` states. Consequently
this is the complete existing `KPApartmentData` record, including its
valuation orbit and original normalizer stability.

`fieldRestrictApartment_isOmegaCompatible` uses an original
`CentralizerDatum`: its representing inclusion, factorization, and
restriction-evaluation bijectivity stay fixed. Bijectivity upstairs for
the literal base change of its factorization and V6 for every family of
the supplied upstairs apartment are explicit premises. Every downstairs
family has an upstairs witness in the image carrier, so the family-level
descent proves full `IntegerValuation.IsOmegaCompatible` for the whole
constructed downstairs apartment on that original actual centralizer.
The proof neither constructs a new centralizer nor asserts that the
base-changed original torus is maximal split.

The provenance is the existing character base-change identities,
split cocharacter equivalence, and character-normalized centralizer
valuation, followed by the existing full root-valuation and apartment
field-restriction constructions. These are internal derived results.
No initial compatible upstairs valuation or apartment, larger-torus
restriction, building geometry, or supplied integral-model comparison is
constructed here. In particular this module does not prove the host task's
unconditional `BuildingComparisonStatement`.
