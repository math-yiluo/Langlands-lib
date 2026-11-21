# Abelian reduction of a supplied Néron model

`Langlands.AbelianScheme.AbelianReductionStatement` starts from a Néron
model of a given abelian variety over a discrete valuation ring. Its input
includes the actual open identity component in the geometric special
fibre and assumes this component is proper. In a smooth Néron fibre the
identity component is smooth and geometrically connected, so properness
expresses that it is an abelian variety. Properness of the identity
component can be checked over the algebraic closure of the residue field.

The conclusion is that the supplied model is proper and geometrically
connected over the valuation ring. Its existing smooth commutative group
scheme then gives an abelian scheme with the given generic identification.

## Provenance

This is the implication (a) to (b) in Bosch, Lütkebohmert and Raynaud,
*Néron Models* (1990), §7.4, printed p. 183, Theorem 5, using geometric
special fibres and the Library's relative identity-component predicate.
