# Universal coefficient matrices and fixed vectors

This internal construction connects the existing actual group-scheme representations
with their universal affine coefficient matrices. It uses no external structural
criterion for unipotence. Its inputs are a commutative ring object
`R : CommRingCat.{u}`, a group-valued functor `F` on commutative `R`-algebras,
a corepresentation `e` by an algebra `B`, and a finite coordinate type
`n : Type` with decidable equality. The index may be empty. The universe of
the base and its algebras is arbitrary.

The entry definition `coefficientMatrix e ρ` evaluates the affine point
transformation of an actual representation
`ρ : MatrixRepresentation (Corepresented.groupScheme F e) n` at the
universal point `e.homEquiv (𝟙 B)`, and takes the underlying matrix over `B`.
`transformation` abbreviates the published `Corepresented.pointsTrans`;
`matrixPointHom` exposes each component as a monoid homomorphism to
invertible matrices.

`transformation_homEquiv` says that evaluation at a classified affine point
applies its classifying algebra map to each universal matrix entry. This is
the naturality square specialized to the universal point.
`coefficientMatrix_groupSchemeMap` recovers the universal matrix from an
induced group-scheme homomorphism: the published affine point formula and
inverseness of the point comparison identify its value with the original
natural transformation. `coefficientMatrix_toGL` applies this recovery to
`Corepresented.LinearEmbedding.toGL`; evaluation at the identity algebra
map gives back the input coefficient matrix.

`coefficientMatrix_comul` proves
`Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` for `a = coefficientMatrix e ρ` and the
coordinate comultiplication `AffineLinearEmbedding.comul e`. Naturality
at the two tensor inclusions, followed by the group-homomorphism law,
identifies the product with the matrix at the point classified by the
comultiplication. The tensor identity
`(a ⊗ 1)(1 ⊗ b) = a ⊗ b` gives the displayed formula.
`coefficientMatrix_counit` similarly evaluates the identity-point law to
obtain `ε(aᵢⱼ) = δᵢⱼ` for the coordinate counit.

`coefficientMatrix_eq_affineMatrix` identifies the construction with
`ρ.affineMatrix B (𝟙 _)`. The identity algebra map classifies the identity
scheme morphism, by the published affine point comparison.
`scalarMap_affine` identifies the structure map on an affine test scheme
with the algebra structure transported through
`Corepresented.affineSectionsIso`.

Finally `isFixedVector_iff` proves, for every `v : n → R`,
that the published all-test predicate `ρ.IsFixedVector v` is equivalent to
`∀ i, ∑ j, v j • a i j = v i • (1 : B)`.
It starts with the published
`MatrixRepresentation.isFixedVector_iff_universal`, compares the matrix
at the universal scheme point with the affine matrix, and transports the
coordinate equation through the inverse spectrum/global-section ring
isomorphism. This ring map is injective and preserves sums and products,
so it both preserves and reflects the equation. Fixedness is therefore
still required on every relative test scheme, including nonaffine schemes;
the theorem merely supplies an equivalent coordinate test.

These adapters construct no unipotent subgroup theorem and prove no
coalgebra characterization of unipotence. They provide the coordinate
interface needed to apply such a separately proved characterization to
the existing group-scheme predicates.
