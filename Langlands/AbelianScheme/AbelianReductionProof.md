# Abelian reduction of a Néron model

`Langlands.AbelianScheme.abelianReduction` proves
`Langlands.AbelianScheme.AbelianReductionStatement`: a Néron model over a
discrete valuation ring of an abelian variety, whose geometric special fibre
has a proper relative identity component, is proper with geometrically
connected fibres. This is the implication (a) to (b) of Bosch, Lütkebohmert
and Raynaud, *Néron Models* (1990), §7.4, printed p. 183, Theorem 5.

The proof applies
`Langlands.AbelianScheme.abelianReduction_of_properClosedFibre` (module
`Langlands.AbelianScheme.AbelianReductionOfProperClosedFibre`) to
`Langlands.AlgebraicGeometry.smoothDvrProperClosedFibre` (module
`Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreProof`), the proof of
the properness criterion `SmoothDvrProperClosedFibreStatement`.

In that reduction, the relative identity component `H` of the Néron model is
smooth with geometrically connected fibres. Its geometric special fibre is the
supplied proper identity component, and properness descends from the
algebraic closure to the residue field. The properness criterion then makes
`H` proper over the discrete valuation ring, so `H` is an abelian scheme. Its
inclusion into the model is an isomorphism on the geometrically connected
generic fibre. The inverse extends by the Néron mapping property of `H`, and
uniqueness of extensions from the generic fibre shows that the inclusion
itself is an isomorphism. Hence the given Néron model is proper and
geometrically connected.
