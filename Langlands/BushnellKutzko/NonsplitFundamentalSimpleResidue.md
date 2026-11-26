# The residue centralizer of a translating element

Module `Langlands.BushnellKutzko.NonsplitFundamentalSimpleResidue`, namespace
`Langlands.BushnellKutzko.NonsplitSimple`. It imports `NonsplitFundamentalSimpleLayers` and
Mathlib's `AdjoinRoot`.

## Setting

`O` is a discrete valuation ring with fraction field `K` (`[IsDomain O]`,
`[IsDiscreteValuationRing O]`, `[IsFractionRing O K]`), `V` a `K`-vector space and
`S = [𝓛, n, r, b]` a stratum over `O` (`Stratum O K V`). Write `𝔄 = 𝓛.order`,
`𝔓 = 𝓛.firstFiltrationIdeal`, `e = e(𝓛)` and `ℛ = S.residueCentralizer ⊆ 𝔄/𝔓`, the classes
with a lift `x` such that `bx − xb ∈ 𝔓^{1−n}`. The hypotheses are:

- `B` is a unit with `S.b = B` and `Shifts S.chain (-S.n) B`, that is, `b L_i = L_{i−n}`;
- `ϖ` is a uniformizer of `O`, acting on `V` as the translation
  `𝓛.uniformizerStabilizer hϖ` of shift `e`;
- `N : ShiftParameters e (-n)` is a Bézout normalization `e = hg`, `−n = gk`, `uk + vh = 1`
  (module `CriticalDerivedNormalization`).

Inside the translation group `𝓛.stabilizer`, `residualStab` is `y = b^h ϖ^{−k}`, of shift zero
(`residualStab_shift`), and `shiftStab` is `τ = b^u ϖ^v`, of shift `g` (`shiftStab_shift`); they
commute. `residualOrder` is `y` as an element of `𝔄`, and `layerCentralizer j` is the
centralizer of its action on the layer `L_j/L_{j+1}` in `End_O(L_j/L_{j+1})`.

## Main results

- `mem_residueCentralizer_iff_commutes`: for `x ∈ 𝔄`, the class of `x` lies in `ℛ` exactly
  when the layer actions of `x` commute with `b` (`LatticeChain.layerAction_commutes_iff` with
  shift `−n`).
- `residueCentralizerEquiv : ℛ ≃+* Π_{j ∈ [0, g)} layerCentralizer j`, sending a class to its
  actions on the layers at `0 ≤ j < g`.
- `isSemisimpleRing_of_aeval_mem`: if `P ∈ O[X]` has irreducible reduction in the residue field
  and `P(y) ∈ 𝔓`, then `ℛ` is a semisimple ring.
- `aeval_mem_of_isSemisimpleRing`: if `ℛ` is semisimple and `P(y)^m ∈ 𝔓`, then `P(y) ∈ 𝔓`.

## Proofs

The translations commuting with a family of layer endomorphisms form a subgroup. Since
`b = τ^k y^v` (`ShiftParameters.reconstruct`) and `ϖ = τ^h (y^u)^{−1}`
(`ShiftParameters.shift_carry`), a family commutes with `b` and `ϖ` exactly when it commutes with
`y` and `τ` (`residual_shift_mem`, `bStab_uniformizer_mem`). Layer actions of elements of `𝔄`
always commute with `ϖ` (`LatticeChain.layerAction_commutes_uniformizer`).

*The isomorphism.* For a class in `ℛ`, the layer actions of a lift commute with `y`, so its
action on `L_j/L_{j+1}` lies in `layerCentralizer j` (`residueLayerHom_mem`). Injectivity
(`residueLayer_injective`): the difference of two lifts has layer actions commuting with `τ` and
vanishing at `0 ≤ j < g`, hence vanishing everywhere by `eq_zero_of_commutes`, so it lies in
`𝔓`. Surjectivity (`residueLayer_surjective`): given centralizing endomorphisms at
`0 ≤ j < g`, `extendFamily` along `τ` gives a family commuting with `τ` and `y`, hence with `ϖ`
and `b`. The Library lifting lemma `LatticeChain.exists_order_lift_layers` gives `x ∈ 𝔄` with
these layer actions, and its class lies in `ℛ`.

*Semisimplicity.* Let `I` be the kernel of `O[X] → k[X] → k[X]/(P̄)`, where `k` is the residue
field. It is maximal because `P̄` is irreducible. If `q ∈ I`, then `q = P s + r` with the
coefficients of `r` in the maximal ideal, so `q(y) ∈ 𝔓` (`aeval_mem_firstFiltrationIdeal`) and
`q` kills the action of `y` on every layer. The layers are finite over `O`, as quotients of
finitely generated lattices, so `isSemisimpleRing_centralizer` (module
`NonsplitFundamentalSimpleAlgebra`) makes each `layerCentralizer j` semisimple. A finite
product of semisimple rings is semisimple, and `residueCentralizerEquiv` transports this to `ℛ`.

*The converse.* If `ℛ` is semisimple, so is each factor `layerCentralizer j`. In it the action
`P(φ_j)` of `P(y)` is nilpotent, since `P(y)^m ∈ 𝔓`, and central, since `P(φ_j)` commutes with
everything commuting with `φ_j`. By `eq_zero_of_isNilpotent_of_commute` it is zero. Thus the
layer actions of `P(y)` vanish at `0 ≤ j < g`. As `P(y)` commutes with `τ`, they vanish
everywhere, so `P(y) ∈ 𝔓`.

## Provenance

This is the computation of the residue centralizer in Bushnell–Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), §2.5, printed pp. 79–83 (PDF pp. 91–95), literature ID
`bushnell-kutzko-1993-admissible-dual-gln`. Before (2.5.10), BK93 computes `ℛ`, for a stratum in
standard form, as the product over a set of coset representatives of the centralizers of the
diagonal blocks. They also show that it is semisimple exactly when these blocks are semisimple.
The Lean proof does not use block matrices or a standard form. The cyclic permutation of the blocks
is replaced by transport along the translation `τ`, and the blocks by the action of `y` on the
layers.
