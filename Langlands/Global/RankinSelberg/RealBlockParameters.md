# Real block lists with fixed discrete data and varying exponents

The continuation arguments of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1,
pp. 53–54, move the inducing exponents of a standard module holomorphically while the discrete
data stay fixed. This module provides that parametrization for the Library's real
presentations (`RealBlock` lists). It also shows that the real pair `L`- and `ε`-factors depend
holomorphically on the exponents. It is the real counterpart of the complex character lists
`ComplexCompactProfileFamily.characterList` and of the holomorphy lemmas in
`ComplexPairParameterReflection`.

## Definitions

- `Shape := Fin 2 ⊕ ℤ` is the discrete datum of a real block: a parity for a real character, or
  a weight for the real induction of a complex character.
- `blockOfParams x t` is the block with datum `x` and complex exponent `t`. A parity `e` gives
  `RealBlock.character (charData e t)`, the character `x ↦ sgn(x)^e |x|^t`. A weight `l` gives
  `RealBlock.induced (characterOfParams l t)`, the real induction of
  `z ↦ (z/|z|)^l |z|^(2t)`.
- `blockList sh p` is the list `[blockOfParams (sh 0) (p 0), …, blockOfParams (sh (n-1)) (p (n-1))]`.
- `tensorShape x y` lists the discrete data of the blocks of `x ⊗ y`, following
  `RealBlock.tensor`:
  - two parities add;
  - a character tensored with an induced block keeps the weight;
  - two weights `l`, `l'` give the weights `l + l'` and `l - l'`.
- `dualShape` fixes parities and negates weights.

## Results

- `realCharacterData_ext` and `complexCharacterData_ext`: a real (or complex) character datum is
  determined by its parity (or weight) and its exponent. The proof uses the field
  `character_eq`.
- `tensor_blockOfParams`: the tensor product of `blockOfParams x t` and `blockOfParams y t'` is
  the list of `blockOfParams z (t + t')` for `z` in `tensorShape x y`. Each case compares parity
  or weight and exponent with the definitions of `RealCharacterData.mul`,
  `ComplexCharacterData.twistReal`, `ComplexCharacterData.mul` and
  `ComplexCharacterData.conj`.
- `dualBlock_blockOfParams` and `map_dualBlock_blockList`: the dual block (the inverse inducing
  character) of `blockOfParams x t` is `blockOfParams (dualShape x) (-t)`. Hence the dual list of
  `blockList sh p` is the parametrized list of the dual data at the negated exponents.
- `lFactor_blockOfParams`: the reciprocal `L`-factor of `blockOfParams x t` at `s` equals the one
  of `blockOfParams x 0` at `s + t`. Both are shifted reciprocal Gamma factors.
- `epsilon_blockOfParams`: the same translation law holds for the block epsilon factor at any
  additive parameter `b` and scale `c`. The exponent enters the determinant value through
  `|b|^t` for a character and `|b|^(2t)` for an induced block. These combine with the power of
  `|b|` in the epsilon factor.
- `pairDenominator_blockList` and `pairEpsilon_blockList`: for two parametrized lists, the pair
  reciprocal `L`-factor and the pair epsilon factor are finite products, over `i`, `j` and the
  data in `tensorShape (sh i) (sh' j)`, of the exponent-zero block factors at `s + (p i + q j)`.
- `differentiable_pairDenominator` and `differentiable_pairEpsilon`: if the exponents
  `p`, `q` and the spectral variable `s` depend holomorphically on a parameter in a complex
  normed space, so do both pair factors. Each factor in the product is an entire function, or
  the differentiable block epsilon, composed with a holomorphic argument.

## Provenance

This is internal infrastructure for the real port of the complex continuation in the inducing
exponents. It makes no claim about integrals.
