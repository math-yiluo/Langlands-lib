# Local action quotients from all-test families of representatives

This internal derived construction starts with an action of a group scheme `A`
on an actual scheme `X` over an arbitrary base `S`. A local base scheme `U`, a
scheme `M` with a morphism `π : M → U`, and a family `s : M → X` are supplied.
The hypothesis is that every point of `X × U` on every relative test has a
unique expression consisting of an `A`-point acting on a member of that family,
together with its prescribed image under `π`.

The orbit family is an actual scheme morphism from `A × M` to `X × U`.
The all-test bijection makes it an isomorphism by Yoneda. The local class map
is the second projection after its inverse. It retains the given `U` coordinate
and is invariant under the action on `X`. Its exact kernel on every original
test is equality of the `U` coordinates together with an acting-group point
relating the `X` coordinates. The proof writes the difference as the quotient
of the two group coordinates. It uses no lift to a different group.

Flatness and local finite presentation of the acting group's structure morphism
pass to the class map through base change and composition with an isomorphism.
The group identity gives a section of the product projection, hence
surjectivity of the class map.

`quotientRepresentationOfLocalSections` applies these results on an fppf
covering sieve of `S`. It assumes a free action on all tests, a flat and locally
finitely presented acting group, and such a family over each member of the sieve.
Each supplied `M → U` must be separated, locally quasi-finite and locally of
finite type. The constructed local class maps satisfy the hypotheses of
`quotientRepresentationOfLocalPresentations`, which descends their represented
parameters to an actual representation of the canonical fppf quotient sheaf.

`GroupIsomorphismScheme.outerOfLocalSections` specializes this construction to
the existing inverse-precomposition action of a faithful automorphic action on a
supplied isomorphism scheme. Quasi-compactness of the acting group, in addition to
the preceding hypotheses, lets `outerOfQuotientRepresentation` give the actual
outer quotient with its flat, surjective and quasi-compact class morphism and
unique same-test acting point for equal classes.

This is a general local adapter for effective quotient descent, derived from
the existing action laws, scheme limits, Yoneda and the quotient representation
and geometry constructors. The families, covering sieve and all-test
decompositions are hypotheses. The module does not produce pinned
classifications or prove existence of the local families for reductive groups.
