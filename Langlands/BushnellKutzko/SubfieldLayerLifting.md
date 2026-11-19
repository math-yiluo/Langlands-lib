# Lifting layer maps over a normalizing field

The extension chain has a period equal to the original chain's shift
under the extension uniformizer. A family intertwining all field units
commutes with every nonzero extension residue scalar, since each such
scalar lifts to an integer-ring unit. Its maps are therefore linear
over the extension integers on the layers. The action of the extension
uniformizer gives the compatibility required by the lifting lemma.
Applying that lemma on the extension chain gives a field-linear lift
with the prescribed action on the original layers.

`SubfieldLayerLiftStatement` records this lifting property over a
nonarchimedean local field. The proof obtains the discrete valuation
ring and the field of fractions properties from finiteness of the
extension inside the endomorphism algebra.

This is a derived step in the proof of Bushnell–Kutzko (1993), (1.4.15),
printed p. 41, using the extension chain from §1.2, printed pp. 24–25.
