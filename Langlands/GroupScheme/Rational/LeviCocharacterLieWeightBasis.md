# A weight basis of the Lie algebra adapted to a parabolic and a Levi subgroup

Module `Langlands.GroupScheme.Rational.LeviCocharacterLieWeightBasis`, namespace
`Langlands.GroupScheme`.

## Contents

- `Gm.powerHom_gmEndEquiv`: every character `χ` of `𝔾_m` over a field is the power map
  `Gm.powerHom _ (gmEndEquiv k χ)`.
- `le_span_basis_coe`: a submodule lies in the span of the ambient images of any basis of it.
- `exists_leviCocharacterLieWeightBasis`: let `G` be connected reductive over a field `k`,
  `q : Q ⟶ G` a parabolic subgroup with geometric unipotent radical `iV : V ⟶ Q` and rational
  Levi subgroup `l' : M' ⟶ Q` (all with affine structure morphisms). There are a central
  cocharacter `ψ : 𝔾_m ⟶ M'` such that `q` represents the dynamic parabolic
  `P_G(ψ ≫ l' ≫ q)`, a `k`-basis `e` of `lieKernel G k` indexed by `Fin n` and integer weights
  `w` such that every `e i` lies in the weight space of `t ↦ t ^ (w i)` for the action of `𝔾_m`
  through `ψ ≫ l' ≫ q`, the `e i` with `w i = 0` lie in the image of `lieKernel M' k` and span a
  subspace containing it, and the `e i` with `w i > 0` lie in the image of `lieKernel V k` and
  span a subspace containing it.
- `exists_leviCocharacterLieWeightBasis_baseChange`: under the same hypotheses, there are a
  central `ψ` presenting `q` as above, `n` and `w` that work over every commutative `k`-algebra
  `A` in the universe of `k`. There is an `A`-basis `e` of `lieKernel G A` such that
  `adjoint G A (t ≫ ψ ≫ l' ≫ q) (e i) = (t ^ (w i)) • e i` for every point `t` of `𝔾_m` over `A`
  (written with `Lie.characterValue`). The spanning properties hold for the images of
  `lieKernel M' A` and `lieKernel V A`.

## Proof

`leviCocharacterLieWeights` (module `Langlands.GroupScheme.Rational.LeviCocharacterLieWeights`)
gives `ψ` with the image of `Lie M'` the weight-zero space and the image of `Lie V` the sum of
the positive weight spaces. The weight spaces of the split torus `𝔾_m` form an internal direct
sum (`isInternal_weightSpace_of_isSplitTorus`). Collecting bases of the weight spaces
(`DirectSum.IsInternal.collectedBasis`) and reindexing by `Fin n` gives `e`, with `w i` the
integer of the weight of `e i` (`gmEndEquiv`). The spanning statements follow from
`le_span_basis_coe` applied to each weight space. For the change of coefficients, `e` is
replaced by `kernelBaseChangeBasis`. The eigenvector property is the definition of the weight
spaces (`mem_weightSpace`), which quantifies over all test algebras. The spanning statements
follow from `lieKernelMapLinear_mem_range_targetMapLinear` and
`range_targetMapLinear_le_span_of_le_span`.

The decomposition is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition 2.1.8 (1), written in a basis.
