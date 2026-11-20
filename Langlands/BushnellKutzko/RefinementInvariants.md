# Ramification index and residue degree from approximation

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). In the book,
equality of `e` and `f` between `F[β₁]` and `F[β, c]` comes from the structure theory of
(1.2.x). Here it is derived directly from the Library's shift homomorphism
`LatticeChain.fieldShift` (`LatticeChainShifts`, `SubfieldLatticeChain`,
`SubfieldValuationShifts`).

## Setting

`F` is a nonarchimedean local field, `𝓛` a lattice chain over `𝒪[F]` in `V`, and `K`, `K'`
fields acting on `V` (`IsScalarTower F K V`) whose units normalize `𝓛`. `Approx` is from
`RefinementCore`: `Approx X Y` means that every element of `X ∩ 𝔓^t` is congruent mod
`𝔓^{t+1}` to an element of `Y`.

## Results

- `subfieldEmbedding_unit_mem_iff`: the action of a unit `a` lies in `𝔓^k` iff `k ≤ shift(a)`.
- `exists_fieldShift_eq_of_approx`: if `K` is approximated by `K'`, every shift of a unit of
  `K` is the shift of a unit of `K'`. An approximant of exact depth `shift(a)` is found and its
  depth read off.
- `mem_subfieldIntegers_of_mem`: if `a ∈ K` acts in `𝔄 = 𝔓^0`, then `a ∈ 𝔬_K`. Write
  `a = u ϖ^n` (`subfieldUnit_factorization`). Its shift is `n · shift(ϖ)` with `shift(ϖ) > 0`,
  so `n ≥ 0`.
- `mem_subfieldMaximalIdeal_iff`: for `a ∈ 𝔬_K`, `a ∈ 𝔭_K` iff `a` acts in `𝔓^1`. Units of
  `𝔬_K` have shift `0` (`fieldShift_integerUnit`). An element of shift `0` is an integer unit
  (`exists_integerUnit_of_fieldShift_zero`).
- `subfieldRamificationIndex_eq_of_approx`: suppose `K` and `K'` approximate each other. The
  uniformizer shifts `d_K` and `d_{K'}` then divide each other. Both are positive, so they are
  equal. Since `d_K · e(K|F) = period = d_{K'} · e(K'|F)`
  (`fieldShift_uniformizer_mul_ramification`), the ramification indices agree.
- `residueQuotient`, `integerAction` and `residueAction`: the `𝒪[F]`-linear map
  `𝔬_K → 𝔓^0/𝔓^1`, `a ↦ [a]`. Its kernel is `𝔭_K` (`ker_residueAction`). Approximation at
  level `0` makes its range contained in that of `K'` (`range_residueAction_le`).
- `residueRingEquivRange`: `𝔬_K/𝔭_K ≃ range(residueAction)` as `𝒪[F]`-modules.
- `subfieldResidueDegree_eq_of_approx`: two-way approximation makes the two ranges equal. Since
  `f(K|F)` is the `𝒪[F]`-length of `𝔬_K/𝔭_K` (`subfieldResidueDegree`), the residue degrees
  agree (`LinearEquiv.length_eq`).
