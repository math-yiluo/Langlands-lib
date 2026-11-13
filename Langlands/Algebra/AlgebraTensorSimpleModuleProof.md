# The algebra tensor-product Scholium

Module `Langlands.Algebra.AlgebraTensorSimpleModuleProof` proves
`Langlands.algebraTensorScholium`, of exact type
`Langlands.AlgebraTensorScholiumStatement.{u₁, u₂, v, v₁, v₂, w₁, w₂}`.
All seven universe parameters are independent and retain the order of the
published target.

The target formalizes the three assertions of Renard III.1.14, Scholium:
simplicity of the external tensor of finite-dimensional simple modules over
unital complex algebras, existence of such a factorization for every
finite-dimensional simple module over their tensor algebra, and uniqueness
of the factors up to module isomorphism. Its paired statement Markdown
records the source and the interpretation of the printed product notation.

The implemented proof constructs the conjunction from three exact theorems:

- `algebraExternalTensorSimple`, in
  `Langlands.Algebra.AlgebraExternalTensorSimpleProof`, obtains every
  complex-linear endomorphism from the external algebra action using the
  published Burnside lemma and the finite-dimensional tensor-Hom equivalence.
  Rank-one maps then force each nonzero stable subspace to be the whole
  tensor space.
- `algebraTensorSimpleFactorization`, in
  `Langlands.Algebra.AlgebraTensorSimpleFactorizationProof`, chooses a
  simple submodule for the first algebra and uses its intertwiner
  multiplicity space for the second factor. Evaluation is an intertwining
  equivalence; a basis and Burnside prove injectivity, and simplicity of
  the given module proves surjectivity and simplicity of the multiplicity
  space.
- `algebraTensorFactorUniqueness`, in
  `Langlands.Algebra.AlgebraTensorFactorUniquenessProof`, proves exactly
  the factor-uniqueness assertion for an intertwining complex-linear
  equivalence of the external tensor spaces. Its paired Markdown describes
  that module's proof.

The final module adds only the conjunction constructor. The helper modules
contain the mathematical proofs and document their derived constructions.
The published target and its imports are unchanged. This is the
algebra-module Scholium; the group-representation statements are separate
results.
