# A proper unitary Jacquet witness from a nonstrict tempered exponent

This internal construction completes the boundary argument for normalized
Jacquet exponents. Given a tempered representation, a specified actual
parabolic decomposition and split component, a compatible root presentation,
and a normalized exponent whose real part belongs to the nonnegative cone
but not to the positive cone, `boundaryUnitaryJacquetWitness` constructs an
actual proper parabolic with a specified unitary normalized Jacquet exponent
of the original representation.

`ProperUnitaryJacquetWitness` records the outer parabolic, rational Levi,
matching geometric unipotent radical, their actual multiplication
isomorphism, a split component, properness, and the actual unitary exponent.
Its exponent implies that the original unitary Jacquet part at this proper
parabolic is nonzero.

The proof first compares the constructed boundary cocharacter with an
arbitrary compatible presentation of the actual boundary parabolic. Both
cocharacters define the same dynamic parabolic on all test schemes. Each
root in the boundary support pairs to zero with the constructed cocharacter.
Applying the published root-sign criterion to the root and its negative
forces its pairing with the transported outer cocharacter to be both
nonnegative and nonpositive. Thus the original boundary support lies in
the outer presentation's actual zero face.

The previously constructed boundary models supply actual nested outer and
inner decompositions retaining the original fine Levi. Existence of a split
component of the connected reductive outer Levi is the published split
component theorem. The definition of normalized-exponent temperedness
supplies a compatible presentation for that actual outer triple. The face
comparison and the published boundary-unitary-exponent construction then
produce the recorded exponent. That construction uses actual normalized
Jacquet transitivity and exponent projection and proves zero real part by
restriction to the outer split component.

The provenance is derived internal work for the reverse direction in
Renard VII.2.4. No independence of restricted simple roots or realization of
arbitrary simple-root subsets is assumed. This construction does not assert
Casselman's analytic criterion or the full square-integrability equivalence.
