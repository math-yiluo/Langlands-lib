# The ordinary induced character formula from the twisted one in degree one

Henniart–Lemaire (2011), II.4.5, printed p. 88 (PDF p. 96), note that the
untwisted formulas are obtained from the twisted ones by replacing `E` by `F`
and `σ` by the identity. This module proves that implication for the Library's
two statements of formula (3):

```text
InducedCharacterFormulaFromTwistedStatement.{u, uV} :=
  TwistedInducedCharacterFormulaStatement.{u, u, uV} →
    InducedCharacterFormulaStatement.{u, uV}
```

`inducedCharacterFormula_of_twisted` proves it. The twisted formula is a
premise. The module proves neither formula.

## Declarations

- `oneSigmaIntertwiner n π : SigmaIntertwiner (1 : F ≃ₐ[F] F) n π` is the
  identity linear equivalence, an isomorphism of `π` with its pullback along
  the entrywise action of `σ = 1` (`entrywiseAut_one_apply`).
  `oneSigmaIntertwiner_toLinearMap` records that its linear map is the
  identity (definitional).
- `leviTensorIntertwiner_one_toLinearMap`: the tensor product
  `leviTensorIntertwiner 1 B` of the identity intertwiners of the blocks has
  linear map `1`. Its linear map is `PiTensorProduct.map` of the identities,
  and Mathlib's `PiTensorProduct.map_id` applies.
- `inducedSigmaIntertwiner_one_toLinearMap`: the induced intertwiner
  `inducedSigmaIntertwiner 1 B` of the identity intertwiners has linear map
  `1` on the normalized product induction of a nonarchimedean local field.
  Evaluated at `x`, the transported function is
  `(A₁ ⊗ ⋯ ⊗ A_r)(ξ(x^{σ⁻¹}))` (definitional, `eval_inducedSigmaIntertwiner`).
  Here `x^{σ⁻¹} = x` entrywise, and the tensor product is the identity by the
  previous item.

## Proof implemented in Lean

Let `F` be a nonarchimedean local field, `n > 0`, `B` a block shape, `π i`
irreducible admissible block representations, `γ` regular semisimple, `m` a
Levi class system for `γ`, and `a j` character values of the Levi tensor
representation at `m j`. Apply the twisted statement with:

- `E = F` (with `Algebra.id` and Mathlib's instance
  `IsTopologicalSemiring.toIsModuleTopology`), `σ = 1`, `l = 1`; the Library's
  `isCyclicAlgebra_one` gives `IsCyclicAlgebra 1 1`;
- the block representations `π i` and the intertwiners `oneSigmaIntertwiner`;
- `δ = γ`. For `l = 1` the norm is `cyclicNorm 1 1 g = g`
  (`cyclicNorm_succ`, `cyclicNorm_zero`, `entrywiseAut_one_apply`), and
  `baseChange F F r g = g` entrywise. So `IsNormAssociated 1 1 γ γ` holds with
  conjugator `1`;
- `d = m`. The first condition on `d j` is the first clause of
  `IsLeviClassSystem` after `entrywiseAut_one_apply`; the second is
  `cyclicNorm 1 1 (m j i) = baseChange F F _ (m j i)`, both sides being
  `m j i`;
- `b = a`. The Levi twisted values at `m j` for the identity tensor
  intertwiner are the ordinary values, by
  `leviTensorIntertwiner_one_toLinearMap` and
  `hasTwistedCharacterValue_one_iff`.

The conclusion is a twisted character value at `γ` of the normalized product
induction for its induced intertwiner. By
`inducedSigmaIntertwiner_one_toLinearMap` that intertwiner is `1`, and
`hasTwistedCharacterValue_one_iff` turns the conclusion into the ordinary
character value `∑ j, relativeDiscriminantWeight B (m j) * a j` at `γ`.

The topological instances on the block groups and on `GL_n(F)` are the
`LocalFieldTopology` certificates, as in both statements.
