# Restriction of group-valued cocycles

This internal helper transports the published all-test cocycle definition without
changing its convention. `comap` precomposes both cover points with a morphism of
covers over the same base. `baseChangeAlong` combines such a morphism with change
of the base, reading group points through `baseChangePointsEquiv`.

The naturality and cocycle identities follow from the corresponding identities of
the original cocycle and the natural multiplicative point equivalence. For a
monomorphic base map, triviality after change of base implies triviality on the
same cover viewed over the old base. To prove this last assertion, any two old-base
maps to the cover give the same map to the new base, because its inclusion is
monic. They are therefore tests over that new base. The new-base coboundary
identity, transported to group points over the old base, gives the desired one.
