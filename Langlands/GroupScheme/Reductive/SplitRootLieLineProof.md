# Proof: root Lie spaces of split maximal tori are lines

This module proves `SplitRootLieLineStatement.{u}` (stated in
`Reductive/SplitRootLieLineStatement`) as the theorem
`Langlands.GroupScheme.splitRootLieLine`. Let `k : Type u` be any field,
`G` a connected reductive group scheme over `Spec k`, `T` a split torus and
`i : T.toGrp ⟶ G` a maximal torus. Then for every `χ ∈ roots i` there is a
`k`-linear equivalence `k ≃ₗ[k] weightSpace i χ`. The universe `u` is
arbitrary. The proof adds no perfectness, characteristic or
algebraic-closedness hypothesis.

## Proof

The theorem is one application of
`rootLieLine_of_twoStructuralInputs` (`Reductive/RootLieLineFromTangent`).
That theorem gives the pointwise conclusion of the statement for the same
field, group, torus, maximal torus and root. Its only extra hypotheses are
two structural propositions, and this module supplies published proofs of
both:

1. `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u}`
   (`Dynamic/CentralizerReductiveProof`). Over any field, a closed
   representative of the centralizer of a cocharacter in a connected
   reductive group is connected reductive.
2. `maximalTorusBaseChange : MaximalTorusBaseChangeStatement.{u}`
   (`Torus/MaximalBaseChangeProof`, Milne 2017, Theorem 17.82). A closed
   torus in a smooth affine group is maximal exactly when its base change
   to a field extension is maximal.

The route inside `rootLieLine_of_twoStructuralInputs` is as follows.

- *Scalar extension.* It base changes `G`, `T`, `i` and `χ` to the
  algebraic closure `K` of `k`. `G_K` is connected reductive, `T_K` is
  split, and `i_K` is maximal by the forward direction of
  `maximalTorusBaseChange`. The base-changed character is still a root
  (`mem_roots_baseChange_iff`).
- *Tangent bound over `K`.* `absoluteRootTangent_le_one_of_structuralInputs`
  bounds by one the dimension of the intrinsic tangent space of the root
  subgroup functor of `χ_K`. Its inputs are the published proofs
  `solvableProperFixedPoint`, `projectiveTorusFixedPointDimension` and
  `solvableTorusQuotient`, together with `dynamicCentralizerReductive`.
  The weight space of `χ_K` lies in this tangent space
  (`RelativeRoot.weightSpace_le_tangentSubmodule_subgroup`). It is nonzero
  because `χ_K` is a root, and it is finite dimensional because `G_K` is
  smooth and affine. So it has dimension exactly one.
- *Descent.* `weightSpace_line_baseChange_iff`
  (`Torus/WeightSpaceScalarExtension`) identifies the base-changed weight
  space with the scalar extension of the original one. It therefore
  reflects the existence of a line trivialization back to `k`.

## Provenance

This is an internal deduction from Library results. Its target restates
the opening field discussion of Conrad, *Reductive group schemes* (2014),
§5.1, printed/PDF p.136: for a split maximal torus of a connected reductive
group over a field, every occurring nontrivial Lie weight space is
one-dimensional. The implemented proof does not follow a single source
argument. It combines the cited Library theorems: reduction to an
algebraically closed field, a bound on the root tangent space by the
structural results above, and descent of the line property along scalar
extension. Worker 1333 wrote the assembly `rootLieLine_of_twoStructuralInputs`.
This module adds only the final substitution of the two structural proofs.
It claims nothing beyond `SplitRootLieLineStatement.{u}`.
