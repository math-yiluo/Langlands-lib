# Lattice boxes and character sums for the mirabolic radical

Author: Worker 806.

This module collects elementary lemmas used by the proofs that the unnormalized
`Φ⁻` functor preserves irreducibility (`MirabolicMinusIrreducibleProof`) and transfers
invariant pairings (`MirabolicMinusPairingTransferProof`). Its content is internal
proof infrastructure: standard facts about lattices in a p-adic field and about finite
character sums, stated in the forms those proofs need. No literature statement is
formalized here.

Throughout, `F` is a p-adic field with topological data `T`, `π^(-N) O` is the Library
lattice `T.additiveLattice N`, and `n(ψ)` is the additive conductor
`T.additiveConductor ψ` of a unitary additive character `ψ`, so that `ψ` is trivial on
`π^(-n(ψ)) O`.

## Character sums

- `sum_out_eq_zero`: let `L` be a subgroup of finite index of an additive group `G`,
  and `χ : G → ℂ` an additive character that is trivial on `L` but not identically
  one. Then the sum of `χ` over a fixed set of coset representatives of `G ⧸ L` is
  zero. The proof translates the sum by a coset where `χ ≠ 1`.
- `eq_one_of_smul_eq_self`: in a complex vector space, `a • v = v` with `v ≠ 0`
  forces `a = 1`.

## Lattice boxes

- `latticeBox T k N`: the additive subgroup `(π^(-N) O)^k` of `F^k`, as
  `AddSubgroup.pi` of the Library lattices.
- `mem_latticeBox`, `coe_latticeBox`: membership is coordinatewise.
- `latticeBox_mono`: the box grows with `N`.
- `isOpen_latticeBox`, `isCompact_latticeBox`: each box is open and compact in the
  product topology.
- `exists_latticeBox_subset`: every neighbourhood of `0` in `F^k` contains a box.
- `finite_latticeBox_quotient`: the quotient of one box by another (as subgroup of the
  first) is finite, because an open subgroup of a compact group has finite index.

## Duality under `ψ`

- `inv_mem_additiveLattice_of_notMem`: if `x ∉ π^(-N) O` then `x⁻¹ ∈ π^N O`.
- `exists_ne_zero_mem_additiveLattice`: every lattice `π^(-N) O` contains a nonzero
  element, namely `π^(-N)`.
- `character_mul_eq_one`: `ψ(a x) = 1` for `a ∈ π^(-(n(ψ) - M)) O` and
  `x ∈ π^(-M) O`.
- `character_dotProduct_eq_one`: `ψ(y ⬝ c) = 1` for `y` in the box at level
  `n(ψ) - M` and `c` in the box at level `M`.
- `mem_latticeBox_of_forall_character_eq_one`: conversely, if `ψ(y ⬝ c) = 1` for all
  `y` in the box at level `A`, then `c` lies in the box at level `n(ψ) - A`. The proof
  tests `y = t e_j` and uses the Library lemma
  `mem_additiveLattice_of_forall_mul_eq_one`.

## Local constancy

- `continuous_of_forall_add_eq`: on a topological additive group, a function `f` with
  `f (c + d) = f c` for all `c` and all `d` in a fixed neighbourhood of zero is
  continuous (it is locally constant).
