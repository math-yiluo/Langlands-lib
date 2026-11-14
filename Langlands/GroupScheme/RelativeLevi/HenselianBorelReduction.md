# Conditional Henselian Borel lifting

This derived module reduces Borel existence over a Henselian local ring to the
existing proposition `RelativeBorelSchemeStatement`. That proposition is an
explicit hypothesis throughout the lifting results; this module does not prove
it.

`IsGeometricBorelSubgroup.isRelativeBorelSubgroup` turns an actual geometric Borel
in a connected reductive field group into a relative Borel over the field's
spectrum. On every residue fibre, this is the geometric Borel field-extension
theorem. The remaining conditions follow from smoothness of the Borel,
closedness of its inclusion and affineness of the ambient group.

`exists_relativeBorel_of_borelScheme` starts with an actual geometric Borel in
the closed fibre. Universality of the assumed Borel scheme gives a point over
the residue field. The published smooth Henselian section theorem lifts this
point to a section over the local ring. Pulling the universal Borel back along
that section and identifying the ambient group by the section pullback
isomorphism gives an actual relative Borel. The proof uses only existence from
universality and smoothness of the parameter scheme; uniqueness and properness
are not needed.

`henselianBorelLift` selects actual relative Borel data from this existence
theorem. It returns the source group, its inclusion in the original group and
the relative Borel property. It does not claim a recovery isomorphism with the
chosen closed-fibre Borel.

`henselianFiniteResidueQuasiSplit_of_borelScheme` obtains the required
closed-fibre Borel from the published `finiteFieldQuasiSplit` theorem. Its
conclusion is relative quasi-splitness. It does not provide a finite étale
splitting extension or establish the full
`HenselianFiniteResidueQuasiSplitStatement`.

The provenance is a composition of existing Library results with the explicit
Borel-scheme hypothesis. No new assertion of Borel representability or of
finite étale Henselian extensions is introduced.
