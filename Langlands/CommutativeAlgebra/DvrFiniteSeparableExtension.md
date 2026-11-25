# Finite separable extensions of a complete DVR

Let `R` be a complete DVR and `L` a finite separable extension of its
fraction field. `DvrFiniteSeparableExtension.isDiscreteValuationRing_and_isAdicComplete`
gives the DVR and completeness properties of the actual integral closure
`integralClosure R L`.

The proof identifies `R` with the valuation ring for the maximal-ideal
valuation of its fraction field. Completeness transfers under this
isomorphism. Integrality of the isomorphism and transitivity of integrality
identify the two integral closures in `L`. NYLL’s finite separable extension theorems apply to its `CompleteDVF` bundle.
The adapters in `Langlands.CommutativeAlgebra.FiniteIntegralClosure` take the two fields
explicitly. Their DVR and completeness conclusions transfer across this identification.

`DvrFiniteSeparableExtension.faithfullyFlat` uses integrality of the inclusion
and flatness of a torsion-free module over a DVR.
`DvrFiniteSeparableExtension.residueEquiv` is the canonical residue field
isomorphism when the base residue field is algebraically closed. The
integral closure is finite in the separable case, so the induced residue
field extension is finite and hence trivial.

These lemmas give the base-ring properties for a finite separable
fraction-field extension in the reduced fibre argument of Conrad's
appendix to Prasad and Yu, *On quasi-reductive group schemes*, author
preprint, p. 32. The DVR result is presented for a chosen valuation
in NYLL §M245. See also [Stacks Project, Tag 09E8](https://stacks.math.columbia.edu/tag/09E8).
