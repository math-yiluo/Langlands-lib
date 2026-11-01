# Actual sections and coordinate-algebra dimension

This internal bridge identifies rational points of a finite étale algebra over a separably closed field with its vector-space dimension. Its provenance is Mathlib's finite étale splitting theorem `Algebra.FormallyEtale.equivPiOfIsSepClosed` and rational-point equivalence `Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum`. Both are used directly: the prime spectrum indexes the field factors, and the dimension of the product of fields is the size of this finite index set.

The scalar structure `coordinateAlgebra f` is induced by the actual map on global functions of the structure morphism `f`. For an affine scheme, `sectionsAlgHomEquiv f` sends an actual section to its map on global functions, followed by the canonical global-functions isomorphism for the field spectrum. Its inverse is the spectrum of an algebra homomorphism, followed by the inverse of the canonical affine presentation of the scheme. The proof checks the section equation and both inverse properties through maps on global functions.

`natCard_sections_eq_finrank` applies this equivalence to a finite étale scheme, transfers finiteness and étaleness through the canonical spectrum isomorphism, and then applies the algebra cardinality theorem. The field may be any separably closed field, and the empty affine scheme is allowed.

This bridge does not assert a multiplication degree or a numerical torsion rank. Those geometric obligations remain separate.
