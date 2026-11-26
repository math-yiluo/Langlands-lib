# Fixed apartments for special tori

`compareSpecialTorus` uses maximal split torus conjugacy over the unramified
field to put the prescribed torus into a translated chart of the original
upper building. The valuation class and its centralizer compatibility are
transported by the conjugacy. `conjugateReducedBuildingEquiv_galois`
identifies the two coefficient actions and the same equivalence preserves
the original rational-point action.

The transported lift is fixed by both the coefficient action and the
unramified units of the common split torus. By
`unramifiedTorusUnitFixedApartment` it lies in the original fixed apartment.
`ReferenceApartmentDescent.eq_on_apartment_of_affine_chart` identifies the
parameterizations of this apartment. The affine-equivalence transport gives
the exact range on the translated chart, transports the derivative by the
torus isomorphism, and pulls back the same affine-root set.

`hasUnramifiedApartmentComparison` moves the result to every rational
translate. A torus in a translated chart is conjugated back to one
containing the original split torus. Rational points stay fixed under
scalar extension and coefficient conjugation, so translation intertwines
the comparisons and their fixed loci.

This implements the comparisons in Kaletha and Prasad, §§9.2.2–9.2.3 and
Propositions 9.3.13, 9.3.16 and 9.4.28, with affine roots in the set form.
