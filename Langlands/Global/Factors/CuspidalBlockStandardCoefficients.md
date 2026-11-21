# Standard models for the actual cuspidal block coefficients

For a supplied real or complex place parameter of a cuspidal block, `realStandardCoefficientEquiv` and `complexStandardCoefficientEquiv` identify the standard module with the chosen local factor in `placeDensityModels`. The target is the exact subspace used in the all-place tensor decomposition of the block.

The parameter supplies an injective map of the standard module into the block's automorphic realization. Covariance in real Lie directions extends to the complexified Lie algebra by tensor linearity. The Library proves that the standard module of a cuspidal parameter is irreducible and that the block realization is isotypic for its chosen irreducible local factor. The isotypic embedding theorem gives a nonzero intertwiner from the standard module to that factor. Irreducibility makes the intertwiner bijective.

The equivalences are for the free monoid of the compact and Lie generators, so each preserves the full compact and complexified Lie action at its place. The identification uses the Library's cuspidal standard-module irreducibility and isotypy theorems. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar Levi coefficient setting for this internal comparison.
