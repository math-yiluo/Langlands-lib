# Fourier expansion along the rotations of several disjoint slots

Lean module: `Langlands.Global.RankinSelberg.RealSlotFourier`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. The slots `Slot N`, the Fourier
coefficients `blockFourierCoefficient`, `coeffs`, `withModes`, `modeLists` and the degree bound
`HasDegree` are those of the modules `RealInducedBlockBound`, `RealInducedTorusCore` and
`RealBlockFourierFinite`; the slot sets are those of `RealSlotMatrices`.

## Fourier expansion

- `rotProd L θ` is the product of the block rotations `blockRotation N s.p (θ s.p)` over a list `L`
  of slots, and `modeProd L J θ` the product of the characters `e^{i j θ(s.p)}` over the slots and
  a list `J` of modes. `rotProd_mem`: `rotProd L θ` is orthogonal.
- `hasDegree_blockFourierCoefficient`: for continuous `u`, a Fourier coefficient along a slot
  disjoint from the slots of a list keeps the degree bound along that list
  (`blockFourierCoefficient_comm`).
- `eq_sum_rotProd`: for pairwise disjoint slots, a continuous right `O(N)`-finite function `u` of
  degree at most `D` along them and `k ∈ O(N)`,
  `u(rotProd L θ · k) = (2π)^{-|L|} Σ_{J} coeffs (withModes L J) u k · modeProd L J θ`, the sum
  over the mode lists of length `|L|` with entries of absolute value at most `D` (`modeLists`). The proof is by induction on the list, with
  the one-slot expansion `eq_sum_of_degree` of `RealInducedTorusCore` at each step.

## Slot sets as lists of slots

- `SlotSet.erase S p` removes one slot; `diag_eq_blockMat_mul` and `rot_eq_blockRotation_mul`
  split off the block of the slot `p` as a block matrix of `RealInducedBlockSlice`.
- `mkSlots L h m` is the list of slots at the positions of a list `L`, with weights `m p` and all
  other data zero; `mem_mkSlots`, `length_mkSlots`.
- `rot_eq_rotProd`: if `L` lists the starts of `S` without repetition, then
  `rot S θ = rotProd (mkSlots L h m) θ`.
