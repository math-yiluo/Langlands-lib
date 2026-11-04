# Existence of the split ground-field unipotent radical

This module proves the published target
`Langlands.GroupScheme.SplitUnipotentRadicalExistenceStatement.{u}`: every
smooth connected affine group scheme `G` over a field `k` has a represented
split ground-field unipotent radical, that is, a closed subgroup
`j : V ⟶ G` with `IsSplitUnipotentRadical j`.

The mathematics is Milne, *Algebraic Groups* (2017), Proposition 6.42 and
§16.g, and Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, p.63 (the
`k`-split unipotent radical). A smooth connected normal split unipotent
subgroup that is largest among such subgroups exists because the product of two
smooth connected normal split unipotent subgroups is again one. The Lean proof
takes the largest one to be a candidate of minimal finite coordinate-kernel
height. All declarations are in namespace
`Langlands.GroupScheme.SplitUnipotentRadicalExistence`.

## The reduction to products

`splitUnipotentRadicalExistence_of_productExistence`: the published proposition
`SmoothConnectedNormalFppfProductExistenceStatement.{u}` implies
`SplitUnipotentRadicalExistenceStatement.{u}`. That proposition says that two
smooth connected closed subgroups with normal ranges in an affine group of
locally finite type have a smooth connected represented fppf-local product.

Proof. Let `G` be smooth, connected and affine over `k`. Then `G` is locally of
finite type.

1. `exists_minimal_height_splitCandidate` (Library module
   `SplitUnipotentRadicalMaximal`) gives a split candidate `i : U ⟶ G`, that
   is, a smooth connected normal closed subgroup that is unipotent and split
   unipotent. Its coordinate kernel has height at most that of every other
   split candidate.
2. `isSplitUnipotentRadical_of_minimal_height` reduces `IsSplitUnipotentRadical i`
   to an upper-bound property. Every split candidate `j : V ⟶ G` must have a
   split candidate `p : P ⟶ G` with `range i ≤ range p` and `range j ≤ range p`.
3. For such `j`, the product hypothesis gives `p : P ⟶ G` with
   `IsFppfProduct (range i) (range j) p`, `P` smooth and `P` connected.
   - `p` is a closed subgroup by `IsFppfProduct.isClosedSubgroup`.
   - `range p` is normal by `IsFppfProduct.isNormal` (Library `FppfProductLaws`).
   - The ranges of `i` and `j` lie in `range p` by `left_le` and `right_le`.
4. `P` is unipotent by the published `isUnipotent_fppfProduct` (module
   `Reductive.FppfProductUnipotent`). This uses that `U` and `V` are affine,
   since closed immersions into the affine `G` are affine morphisms over the
   affine base.
5. `P` is split unipotent by `SplitNormalFppfProduct.splitNormalFppfProduct`,
   in the helper module `Reductive.SplitNormalFppfProductProof` submitted with
   this proof.

## The target theorem

`splitUnipotentRadicalExistence : SplitUnipotentRadicalExistenceStatement.{u}`
applies `splitUnipotentRadicalExistence_of_productExistence` to the published
theorem `Langlands.GroupScheme.smoothConnectedNormalFppfProductExistence` from
module `SubgroupFunctor.SmoothConnectedNormalProductExistenceProof`, which
proves `SmoothConnectedNormalFppfProductExistenceStatement.{u}` with no
premises. So the result holds for every field `k : Type u`. It has no
hypotheses beyond those of the target statement and uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
