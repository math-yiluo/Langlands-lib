# Actual splitting of the complex Harris group scheme

This internal construction realizes the all-test-scheme point comparison from `ComplexGroupPoints` as an isomorphism of actual group schemes. It uses the categorical product and point coordinates from `GeneralLinearProduct` and the fully faithful group-valued Yoneda reconstruction in `Multiplicative`.

The inputs are the same central-simple unitary data D and signature charts C as in `ComplexGroupPoints`. The source remains the iterated scalar extension of the rational Harris similitude group to the real and then complex numbers. `complexSplitGroupScheme` is the product, indexed by the real embeddings of E, of GL_n over Spec ℂ, with a single additional Gm. The input charts determine the coordinate isomorphism; they do not supply an assumed group-scheme isomorphism.

`complexSplitPointsEquiv` composes the established Harris point equivalence with the inverse of the product-scheme point equivalence. `complexSplitPointsEquiv_coordinates` identifies its product coordinates with the established Harris coordinates. Naturality follows by applying the injective product coordinates and comparing the two proved entrywise restriction formulas. `complexGroupSchemeIso` then applies `GroupScheme.isoOfPoints` to construct both scheme morphisms, their group-law compatibilities, and their inverse identities.

The forward and inverse point formulas prove that these actual morphisms realize the existing first-matrix coordinates at every real embedding and the common scalar multiplier, on every complex test scheme. The unitary second matrix is still recovered by `complexGroupPointsEquiv_second` in the imported module.

This is a scheme realization of the imported algebraic splitting. Smoothness and reductivity, Galois compatibility of charts, reflex-field identification, and PEL moduli and level-scheme construction remain separate obligations.
