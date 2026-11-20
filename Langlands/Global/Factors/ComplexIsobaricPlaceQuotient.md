# The prescribed isobaric constituent at a complex place

`HasComplexIsobaricPlaceQuotient` takes a family of actual cuspidal realizations
over a number field and one complex place. Each realization has a complex
parameter at that place, and the parameter's compact-finite standard module is
irreducible. The concatenation of these parameters in the supplied order can
be sorted into a list whose standard module has an irreducible quotient. The
same quotient is the target of a surjective intertwiner from a stable
subspace of the standard module in the supplied order.

The proof uses the complex branch of the Library's generic component bridge.
The complex generic standard parameter theorem gives an injective
intertwiner into that component. The standard module is nonzero by the
length condition, so its image is the irreducible component. Composing with
the component map gives the place parameter of the actual cuspidal
realization. Summing the parameter lengths gives the length of the
concatenation. The stable sort and `complexOrderedQuotient_subquotient`
then give the desired constituent with the quotient actions.

This formalizes the complex local part of Getz and Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 10.6.4,
printed p. 286 (PDF p. 298), used in Theorem 10.7.5, printed p. 288
(PDF p. 300). The implementation uses the ordered quotient of Knapp,
*Local Langlands correspondence: the archimedean case* (1994), Theorem
4(a) and (4.3), printed p. 405 (PDF p. 415).
