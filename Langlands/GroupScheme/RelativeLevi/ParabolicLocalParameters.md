# Local parameters from uniform parabolic field types

This internal construction assumes a supplied family of actual relative
parabolic inclusions with uniform rational field-conjugacy types. The base is
an arbitrary scheme in universe `u`, the reductive ambient group is actual,
and the index type lies in `Type u`; no finiteness assumption is needed here.
Existence of uniform types and representability remain separate obligations.

Rational conjugacy of actual subgroup ranges is preserved and reflected by an
ambient group-scheme isomorphism. The proof transports the conjugator through
the isomorphism and applies the all-test range comparison. This also proves
`HasUniformParabolicFieldTypes.baseChange`: the iterated ambient pullback is
identified with the direct one, and naturality identifies every pulled-back
representative. Existence and uniqueness of the index are transported through
that equivalence.

`range_innerIso_inv_of_eq` reverses a range-conjugacy equation by composing
with the inverse inner automorphism. Applying uniform field types at the
residue field of a base point, reversing its conjugator, and invoking the
published etale-local conjugacy theorem proves
`exists_etale_conjugacy_of_fieldTypes`. It supplies an index, an etale
neighbourhood containing the point, and an actual group-valued conjugator of
the chosen representative onto the given inclusion.

`parameterOfIteratedConjugator` sends a conjugator in the iterated pullback
through the canonical ambient pullback comparison and the actual base-point
equivalence. The accompanying range theorem identifies its actual conjugate
family with evaluation of any inclusion satisfying the original conjugacy
equation. The proof composes the range equation with that comparison, uses
naturality of inner conjugation and pullback comparison, and cancels the
source comparison isomorphism.

`EtaleParabolicParameter` records a neighbourhood of a specified point of an
arbitrary test scheme, its etale projection, a point above the original one,
an index in the supplied family, and an actual group-valued parameter. Its
evaluation equation says that the actual conjugate parabolic is the
restriction of the supplied test family.

The existence proof chooses an actual relative-parabolic representative of
the test family. It applies the preceding neighbourhood theorem to the
pulled-back family and the base-changed uniform types. The transported
conjugator satisfies the required evaluation equation by the range theorem
and independence of restriction from the chosen representative.
`etaleParabolicParameter` chooses this data. These are internal consequences
of the imported Library results; no new literature translation is claimed.
