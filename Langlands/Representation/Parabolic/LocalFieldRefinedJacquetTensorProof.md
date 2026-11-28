# Normalized refined Jacquet restriction of external tensors: proof

`Langlands.RefinedJacquetTensor.localFieldRefinedJacquetTensor` proves
`Langlands.RefinedJacquetTensor.LocalFieldRefinedJacquetTensorStatement.{uF, uV}`
with both universe parameters free. It covers every field with
`LocalFieldData`, every block shape `B` (including the empty shape in rank
zero), every refinement `S` and every family `A` of complex representations
of the outer blocks. The equivalence it produces acts on the actual
quotients `T.normalizedRefinedJacquet B S _` and
`T.normalizedJacquet (S i) (A i).ρ`, and on the class of every pure tensor
it is given by the formula in the statement.

## The linear equivalence

The refined unipotent subgroup `refinedUnipotent F B S` is by definition the
product subgroup `Subgroup.pi Set.univ (fun i => (S i).unipotentSubgroup F)`
of the outer Levi. So `RefinedJacquetModule B S _` of the external tensor is
the module of coinvariants of that tensor under a product subgroup.
The private equivalence `productQuotientEquiv` composes two maps.

1. `RefinedOppositeJacquetTensor.coinvariantsEquiv` identifies the
   coinvariants of a finite external tensor under a product subgroup with the
   tensor of the factor coinvariants. It is the trivial-character case of the
   character-localization comparison `FiniteTensor.characterLocalizationEquiv`.
2. `PiTensorProduct.congr` applies, in each slot, the inverse of
   `BlockShape.jacquetModuleEquiv`. That map identifies the parabolic Jacquet
   carrier `(S i).JacquetModule (A i).ρ` with the coinvariants of the ambient
   matrix subgroup `(S i).unipotentSubgroup F`.

`productQuotientEquiv_mk` evaluates the composite on the class of a pure
tensor `⨂ v i`. The first map gives `⨂ Jacquet.mk (v i)` by
`coinvariantsEquiv_mk_tprod`. Rewriting each factor with
`BlockShape.jacquetModuleEquiv_mk` and cancelling the equivalence gives
`⨂ (S i).jacquetMk (A i).ρ (v i)`. This is the pure-tensor clause of the
statement, and the theorem uses it for that clause directly.

## Equivariance

Let `m` be in the refined Levi `refinedLevi F B S`.

- `LocalFieldData.normalizedRefinedJacquet_mk` says that `m` acts on a
  refined class by the scalar `T.refinedLeviInverseHalfModulus B S m` times
  the class of `m.val` applied to the representative.
- `inverseHalf_eq_prod` writes that scalar as the product over `i` of
  `(T.leviHalfModulus (S i) (refinedLeviBlock B S i m))⁻¹`. The proof
  unfolds the inverse half, rewrites with
  `LocalFieldData.refinedLeviHalfModulus_eq_prod` from
  `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization`
  and distributes the inverse over the product. Here
  `T.refinedLeviModulus B S` is by definition the product of the inner moduli
  `T.leviModulus (S i)` on the inner Levi coordinates.
- On the target, `(refinedLeviEquiv F B S).symm m` has `i`-th coordinate
  `refinedLeviBlock B S i m`, the same inner Levi element. In slot `i`,
  `LocalFieldData.normalizedJacquet_mk_eq_inv_halfModulus` gives the factor
  `(T.leviHalfModulus (S i) _)⁻¹` times the class of
  `(S i).leviEmbedding F` applied to the representative.
- `blockEmbedding` shows that this embedding returns the original block
  `m.val i`. The external tensor action of `m.val` on `⨂ v i` is
  `⨂ (A i).ρ (m.val i) (v i)` by `FiniteTensor.external_tprod`.

`productQuotientEquiv_comm` combines these facts for one pure tensor.
`MultilinearMap.map_smul_univ` collects the factor scalars into their product,
which is the refined scalar. The main theorem then proves equivariance on the
whole quotient. Every class is `refinedJacquetMk` of a representative, by
`Jacquet.mk_surjective`. The representative is a sum of scalar multiples of
pure tensors (`PiTensorProduct.induction_on`), and both sides are linear.

For the empty block shape the index type is `Fin 0`. Then the products are
empty, both tensor products are one-dimensional, and the same argument
applies without a separate case.

## Classification dependencies

The proof uses no classification result. This was checked in two ways
against the Library at commit `2f86a99eb5616254ac5b9c399603c9bbbea15f7a`.

**Constants.** A breadth-first scan started at
`localFieldRefinedJacquetTensor`. For each constant it reached, it followed
every constant occurring in that constant's type or value, including the
values of theorems and opaque constants. It ran as an `#eval` in a separate
module, outside the Library, compiled against this module. It reached 26,748 constants in
1,005 modules. Exactly 26 of those modules are `Langlands` modules, and no
reached constant lies in a module whose name contains `Classification`. The
26 modules are:

- this module and `Langlands.Representation.Parabolic.LocalFieldRefinedJacquetTensorStatement`;
- general linear blocks and moduli: `Langlands.Group.GL.Basic`,
  `Langlands.Group.GL.Blocks`, `Langlands.AllField.Group.GL.BlockModulus`,
  `Langlands.AllField.Group.GL.NormalizedCharacter`;
- local-field data: `Langlands.LocalField.LocalFieldData`,
  `Langlands.LocalField.LocalFieldArithmetic`,
  `Langlands.LocalFactor.FML.Valuation`;
- refinements: `Langlands.Representation.Geometric.RefinementDefinitions`,
  `Langlands.Representation.Geometric.RefinementFunctors`,
  `Langlands.Representation.Geometric.WeylDefinitions`,
  `Langlands.AllField.Representation.Geometric.RefinementDefinitions`,
  `Langlands.AllField.Representation.Geometric.RefinementFunctors`,
  `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization`;
- Jacquet quotients: `Langlands.Representation.Jacquet.Coinvariants`,
  `Langlands.Representation.Jacquet.Localization`,
  `Langlands.Representation.Jacquet.Normalized`,
  `Langlands.Representation.Jacquet.Parabolic`,
  `Langlands.Representation.Jacquet.PositiveCharacter`,
  `Langlands.Representation.Jacquet.SmoothTwist`,
  `Langlands.AllField.Representation.Jacquet.Parabolic`;
- tensors and twists: `Langlands.Representation.Tensor.Finite`,
  `Langlands.Representation.Tensor.CharacterLocalization`,
  `Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor`,
  `Langlands.Representation.Twist.Definitions`.

**Imports.** The module imports only the statement module and
`Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization`.
Following `import` lines gives 255 Library modules. Five of them are
classification modules, and the statement module's import closure already
contains all five:

- `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`;
- `Langlands.Representation.Classification.Supercuspidal`;
- `Langlands.Representation.Classification.SupercuspidalContragredientAux`;
- `Langlands.Representation.Classification.SupercuspidalContragredientStatement`;
- `Langlands.Representation.Classification.SupercuspidalTwist`.

The statement module has three imports, and they bring in these modules
along two kinds of route (module names below drop the `Langlands.` prefix):

- `Representation.Parabolic.RefinedOppositeJacquetTensor` reaches exactly
  three of them: `CuspidalJacquetMultiplicityStatement`, `Supercuspidal` and
  `SupercuspidalTwist`. Its import `Representation.Parabolic.OppositeJacquetMap`
  imports `CuspidalJacquetMultiplicityStatement`, which reaches
  `Supercuspidal` through `Representation.CuspidalSupport.LeviDefinitions`.
  Its import `Representation.Parabolic.OppositeRefinementFunctors` reaches
  `SupercuspidalTwist` through `Representation.Parabolic.RefinementComposition`
  and `Representation.Parabolic.RefinementCharacter`.
- `AllField.Representation.Jacquet.Parabolic` and
  `AllField.Representation.Geometric.RefinementFunctors` (the latter through
  its import `AllField.Representation.Geometric.RefinementDefinitions`) each
  reach exactly three of them: `Supercuspidal`,
  `SupercuspidalContragredientAux` and `SupercuspidalContragredientStatement`.
  The route runs through `AllField.Group.GL.BlockModulus`,
  `AllField.Group.GL.NormalizedCharacter`, `AllField.Group.GL.Padic`,
  `AllField.LocalField.Foundation`, `LocalField.LocalFieldArithmetic`,
  `LocalField.LocalFieldData`, `HarmonicAnalysis.GeneralScalarHaarScalingProof`,
  `HarmonicAnalysis.GeneralHaarScalingStatement`,
  `Representation.Shahidi.IntertwiningInduced` and
  `Representation.Category.Contragredient`. The last of these imports
  `SupercuspidalContragredientAux`, which imports
  `SupercuspidalContragredientStatement`, which imports `Supercuspidal`.

The second import of this module,
`AllField.Representation.Parabolic.RefinedInductionTensorNormalization`,
also reaches exactly `Supercuspidal`, `SupercuspidalContragredientAux` and
`SupercuspidalContragredientStatement`. Its import closure contains both
`LocalField.LocalFieldData` and `Representation.Category.Contragredient`, and
it has a further route through `Representation.Smooth.SmallRealizationProof`.
No module under `Langlands.AllFieldBZ` is in the import closure.

All of this concerns `import` lines only. These classification modules are
imported but not used: the constant scan above reaches no constant from any
of them.

## Relation to the literature

The statement page cites Bernstein and Zelevinsky (1977), §§1.8(b), 1.9(g)
and 2.2–2.3. The implemented proof follows the same idea. Jacquet restriction
along a product of unipotent radicals is computed factor by factor on an
external tensor, and the normalizing character of the product is the
product of the normalizing characters. In the Lean proof the first fact is
the coinvariant comparison for product subgroups, and the second is the
product formula for the refined modulus.
