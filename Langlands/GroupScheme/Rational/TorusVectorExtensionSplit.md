# Retractions for split-torus extensions with vector quotient

This is an internal derived construction, transporting the algebraic section in
`CentralTorusVectorExtensionHopf` to actual affine group schemes over any field
`K : Type u`. It adapts the fully faithful Hopf-spectrum transport from
`Torus/CentralExtensionSplit`; it makes no additional literature claim.

For an affine group scheme `E`, an actual central closed inclusion `z : Z → E`,
and an actual fppf quotient `p : E → Q` with kernel the range of `z`, assume
`Z` is isomorphic to a split torus on a finite type `J : Type u`, and `Q`
is isomorphic to a standard finite-dimensional vector group. Then
`exists_retraction_of_split_vector_quotient` proves that there is an actual
group-scheme morphism `r : E → Z` with `z ≫ r = id`.
`retractionOfSplitVectorQuotient` chooses one, and its composition theorem
proves that same identity. No smoothness or characteristic assumption on `E`
is required, and the total group need not be commutative.

The proof uses the chosen affine Hopf coordinates of `E` and `Q`.
`isCentralTorusExtension` converts the geometric data into the algebraic
extension conditions: faithful flatness gives injectivity of quotient
coordinates, the closed inclusion gives surjectivity onto torus coordinates,
the kernel identifies the trivial composite, centrality compares the two
coactions, and quotient descent identifies the invariant subalgebra.

`exists_section_of_polynomial` applies the algebraic section construction when
the quotient algebra is isomorphic to a polynomial algebra. The polynomial
unique-factorization instance transfers to the quotient algebra and makes
its Picard group trivial. Transport of tensor squares and
`PolynomialTensorUnits.exists_eq_smul_one` show that tensor-square units are
scalar. The resulting bialgebra section is a morphism of commutative Hopf
algebras, since the category expresses its morphisms through bialgebra maps.

Finally, the vector-group isomorphism identifies `Q`'s chosen coordinates
with `MvPolynomial (Fin n) K`. The fully faithful Hopf spectrum functor
transports the algebraic section to a retraction of `z`; its functor laws
transport the section identity to the displayed composition identity.
Nonsplit-torus descent and rational-point factorization are separate obligations.
