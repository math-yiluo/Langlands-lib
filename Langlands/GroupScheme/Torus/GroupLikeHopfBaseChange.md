# Base change for group-like-spanned Hopf algebras

This internal helper module defines
`Langlands.GroupScheme.HopfCoordinates.groupLikeBaseChange`, the canonical
homomorphism

`GroupLike R A →* GroupLike S (S ⊗[R] A)`

sending `a` to `1 ⊗ a`, for commutative rings `R`, `S`, `A`, an `R`-algebra
structure on `S`, and a Hopf `R`-algebra structure on `A`. The rings may have
independent universe sizes. No flatness or finiteness assumptions are needed
for this construction.

The supporting lemma `HopfCoordinates.isGroupLikeElem_one_tmul` proves that
`1 ⊗ a` is group-like over `S` whenever `a` is group-like over `R`. Its proof
uses the counit and comultiplication formulas for the tensor-product
coalgebra. Multiplication and identity preservation for `groupLikeBaseChange`
then follow from multiplication of pure tensors.

`HopfCoordinates.span_groupLike_baseChange` proves that if group-like elements
span `A` over `R`, group-like elements span `S ⊗[R] A` over `S`. Every pure
tensor `s ⊗ a` has the asserted membership: express `a` using the original
spanning family, map those expressions to pure tensors, and use that
`s ⊗ g = s • (1 ⊗ g)` for a group-like `g`. Induction on tensors proves the
claim for every element of the scalar extension. This result concerns
spanning; it does not assert that all group-like elements after base change
come from original group-like elements.

`Diagonalizable.finitePresentation_addGroupAlgebra` proves
`Algebra.FinitePresentation R (AddMonoidAlgebra R M)` for any commutative ring
`R` and finitely generated abelian group `M`, including groups with torsion.
The proof first obtains finite type of `ℤ[M]` from finite generation of `M`.
Since `ℤ` is noetherian, finite type implies finite presentation. Finite
presentation survives scalar extension, and
`AddMonoidAlgebra.scalarTensorEquiv ℤ R` identifies that scalar extension with
`R[M]`. This is algebra finite presentation, not module finiteness.

The provenance is internal: these are direct applications of the existing
Mathlib tensor-product coalgebra, monoid-algebra and finite-presentation APIs,
intended for the local-to-open-neighborhood argument in the proof that fppf
closed subgroups of groups of multiplicative type are of multiplicative type. They do not
supply local Hopf reconstruction or a proof of the closed-subgroup theorem.
