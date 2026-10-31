# Continuous actions with varying topological groups

This internal construction retains an actual topological group and an object of
Mathlib's `ContAction TopCat G`. Its arrows consist of a continuous group
homomorphism and a continuous map of the original spaces satisfying the
equivariance equation. The two maps have the same source-to-target direction.
Identity and composition use the corresponding actual maps. Extensionality in
these two maps proves the category laws. Forgetting the group gives a functor to
`TopCat`; the fixed-group functor is faithful and assigns the identity group
homomorphism to every arrow.

This is a topological prerequisite for the actual quotient-spectrum construction
in `GeneralizedAffinoid/VariableAction`. Its motivation is the category of spaces
with operators in Berkovich's unfinished *Etale equivariant sheaves on p-adic
analytic spaces* (1996), section 1.1, printed/PDF pp.2–3. The construction here is
internally derived, and does not define analytic spaces or the topology on their
analytic automorphism groups. The precise source registration and scope are
recorded in that companion.
