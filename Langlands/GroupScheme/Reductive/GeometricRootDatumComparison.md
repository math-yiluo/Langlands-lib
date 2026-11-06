# Comparing actual root data through a geometric group isomorphism

This internal construction supports generic-fibre determination of reductive
group schemes. It uses the published field-level maximal-torus conjugacy and
central-isogeny root-datum theorems on the Library's actual group schemes.

`exists_rootDatumEquiv_of_torusCompatibleIso` starts with connected reductive
groups over a field, chosen split maximal tori and supplied actual root data.
An actual group isomorphism and a torus isomorphism that form a commuting
square produce a contravariant `RootPairing.Equiv`. Its character map is
precomposition with the torus map, and its cocharacter map is composition
with that same map. The proof treats the group isomorphism as a central
isogeny and applies `centralIsogenyRootDatumHom`. The weight map is bijective
by the isomorphism criterion in that theorem. The cocharacter map agrees with
the actual lattice equivalence of the torus isomorphism and is therefore
bijective as well. This controls the entire lattices, including the central
torus directions.

`rootDatumEquivOfTorusCompatibleIso` chooses this full equivalence. Its
`weightMap` and `coweightMap` theorems record the two exact lattice formulas.
This is a derived internal construction from the named published theorems,
with no additional geometric classification assertion.

`nonempty_rootDatumEquiv_of_iso_of_isAlgClosed` removes torus compatibility
over an algebraically closed field. It applies `maximalTorusConjugacy` to
the image of the first chosen maximal torus and the second one. Composing
the original group isomorphism with the supplied inner automorphism gives
the required torus-compatible square. The first theorem then gives an
equivalence, whose inverse has the stated direction.

The root indices and base field have an arbitrary common universe `u`.
There is no restriction on the characteristic or on the central torus.
These are field-level comparison lemmas. This module does not supply
strict-Henselian splitting or classification over an integral base, and it
does not extend a prescribed generic-fibre isomorphism.
