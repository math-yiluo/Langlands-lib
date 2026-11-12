# The dimension identity for a globalized Galois type relation

Author: Worker 126. This supporting unit belongs to Task 5093
(`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`). All declarations are in
`Langlands.LocalFactor.NonabelianBrauer`.

For a `GaloisTypeDecomposition F e z`, each character type gives a relation in
the actual finite Galois representation group. Suppose a Galois extension of
number fields `K'/k` has its Galois group identified with that of the local
normal field by `θ`. The module proves that the global intermediate fields
defined in `GlobalRelation` satisfy

`Σ_{g ∈ supp z} z(g) [globalField(g) : k] ([t₁(g) = τ] - [t₂(g) = τ]) = 0`

as an equality of integers, for every complex type `τ`. The local field
universe and the global number field universe are independent. Neither an
epsilon identity nor a local nonabelian system is assumed.

`globalTypeDimension D k K' θ τ` defines the left hand side as an integer.
`globalTypeDimension_eq_zero` proves its vanishing. The following three lemmas
also expose the intermediate degree calculation and the expanded identity.

`finrank_globalField_eq_galoisImage_index` applies the Galois correspondence:
the degree of the fixed field is the index of its fixing subgroup.
The fixing subgroup of this fixed field is exactly `globalSubgroup`. This is
the inverse image of the local Galois image under `θ`, so its index is the
index of that image.

`galoisType_dimension` evaluates the virtual trace character of `D.identity τ`
at the identity. The trace at the identity is the dimension. The published
`FiniteRep.InducedCharacter.inducedDegree` computes the dimension of induction
as the subgroup index times the dimension of the inducing character line;
that line has dimension one. The resulting complex equality is an equality
between integer casts, hence gives the integer dimension identity.

`globalField_type_dimension` substitutes the field-degree formula into that
integer dimension identity. It supplies the dimension hypothesis needed to
cancel archimedean products type by type.

This is internal bookkeeping derived from the published `GaloisType`,
`GlobalRelation`, and finite induced-degree proof, together with Mathlib's
Galois correspondence and subgroup-index invariance under a surjective map.
Its role in the arithmetic argument is the dimension cancellation used in
Deligne, *Les constantes des équations fonctionnelles des fonctions L*
(1973), proof of Lemma 4.12, printed page 544 (PDF page 44), registered as
`deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The statements here concern only the dimensions of the existing relation.
