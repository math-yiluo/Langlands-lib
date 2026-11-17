# Lattice chains and hereditary orders (Bushnell–Kutzko 1993, §1.1)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.1, printed pp. 19–21 (PDF pp. 31–33; PDF page = printed page + 12).

## Setting

The module works with a commutative ring `O`, a field `K` with an algebra map `O → K`, and a
`K`-vector space `V` that is also an `O`-module through `K` (`[IsScalarTower O K V]`).
Bushnell–Kutzko's case is `O = 𝔬_F = 𝒪[F]`, `K = F` for a nonarchimedean local field `F`. The
generality is used for the `𝔬_E`-lattice chains of BK93 §1.2, where `O = 𝔬_E` is the integral
closure of `𝔬_F` in a field `E` (`SubfieldIntegers`, `SubfieldOrderStatement`), a ring for
which Mathlib provides no `IsLocalRing` instance.

## Lattices (BK93 p. 20)

BK93 defines an `𝔬_F`-lattice in a finite-dimensional `F`-vector space as a compact open
`𝔬_F`-submodule, equivalently a finitely generated `𝔬_F`-submodule containing an `F`-basis. The
module uses Mathlib's `Submodule.IsLattice K`: a finitely generated `O`-submodule whose `K`-span
is all of `V`. For `O = 𝔬_F` this is BK93's second description.

## `LatticeChain O K V` (BK93 (1.1.1), p. 20)

A structure with fields

- `lattice : ℤ → Submodule O V`, the sequence `(L_i)_{i ∈ ℤ}`;
- `isLattice`: every `L_i` is a lattice;
- `lattice_succ_lt`: `L_{i+1} ⊊ L_i` for all `i` ((1.1.1)(i));
- `exists_period`: there is `e : ℕ` with `0 < e` and `L_{i+e} = 𝔭 L_i` for all `i`
  ((1.1.1)(ii)), where `𝔭 L_i` is the ideal-times-submodule product `Ring.jacobson O • L_i`.

BK93 defines a lattice chain as a set of lattices, linearly ordered and stable under `F^×`, and
then shows (p. 20) that this is the same as a sequence satisfying (1.1.1). The structure is the
sequence form, which BK93 calls "the definition commonly used elsewhere". The contract asks for
`e ≥ 1`; in (1.1.1)(ii) `e ∈ ℤ`, and strict decrease forces `e ≥ 1`.

The ideal in (1.1.1)(ii) is `Ring.jacobson O`. For a nonarchimedean local field `F`,
`jacobson_integer_eq_maximalIdeal` proves `Ring.jacobson 𝒪[F] = 𝓂[F] = 𝔭_F`, so for
`O = 𝒪[F]` this is exactly BK93's condition `L_{i+e} = 𝔭_F L_i`. For `O = 𝔬_E`, a discrete
valuation ring when `E/F` is finite, the Jacobson radical is `𝔭_E`.

No field encodes any of the statements S1–S5 of the task.

## The period `e(𝓛)` (BK93 p. 20)

`LatticeChain.period` is the least `e` provided by `exists_period` (`Nat.find`). The module
proves `period_pos`, `lattice_add_period` (`L_{i+e(𝓛)} = 𝔭 L_i`) and `period_unique`: any
`e : ℕ` with `L_{i+e} = 𝔭 L_i` for all `i` equals `e(𝓛)`. This is BK93's statement that `e` is
uniquely determined. Its proof uses injectivity of `i ↦ L_i`, which follows from strict
decrease (`strictAnti`, `antitone`, `injective`).

## `End^n_O(𝓛)` and the order `𝔄(𝓛)` (BK93 (1.1.2), p. 20)

- `LatticeChain.endFiltration 𝓛 n : Submodule O (Module.End K V)` is
  `End^n_O(𝓛) = {x ∈ A : x L_i ⊆ L_{i+n} for all i ∈ ℤ}` for `n ∈ ℤ`, where
  `A = End_K(V) = Module.End K V`. The task's `𝔓^n(𝓛)` is this lattice.
- `LatticeChain.order 𝓛 : Subalgebra O (Module.End K V)` is `𝔄(𝓛) = End^0_O(𝓛)`, an
  `O`-subalgebra of `A`. Its underlying `O`-module is `endFiltration 0` (`toSubmodule_order`,
  by `rfl`), and `mem_order` gives the membership condition `x L_i ⊆ L_i` for all `i`.
- Proved API: `mem_endFiltration`, `endFiltration_antitone`, `mul_mem_endFiltration`
  (`End^m · End^n ⊆ End^{m+n}` elementwise), `mem_order_iff_mem_endFiltration`.

That `End^1` is the Jacobson radical of `𝔄` and that `End^n` is its `n`-th power (BK93 p. 21)
are not proved here. They are part of `RadicalFiltrationStatement`.

## Hereditary and principal orders (BK93 pp. 20–21)

- `IsHereditaryOrder 𝔄` for `𝔄 : Subalgebra O (Module.End K V)` means
  `∃ 𝓛 : LatticeChain O K V, 𝓛.order = 𝔄`. **This is the lattice-chain description, not the
  ring-theoretic definition.** BK93 (p. 20) defines an order to be hereditary if every left
  `𝔄`-lattice is projective. It then recalls from Reiner, *Maximal orders*, without proof, that
  the hereditary `𝔬_F`-orders in `A` are exactly the orders `𝔄(𝓛)`. The module takes this
  description as the definition, as the task permits, and does not formalize the equivalence.
- `LatticeChain.IsPrincipal 𝓛` means the index `(L_i : L_{i+1})` is the same for all `i`
  (BK93 p. 21). The index is `AddSubgroup.relIndex` of `L_{i+1}` in `L_i`.
  `IsPrincipalOrder 𝔄` means `∃ 𝓛, 𝓛.order = 𝔄 ∧ 𝓛.IsPrincipal`.

## Auxiliary result

`jacobson_integer_eq_maximalIdeal F : Ring.jacobson 𝒪[F] = 𝓂[F]` holds for every
nonarchimedean local field `F` (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), because `𝒪[F]` is a local ring.

## Relation to the Library

`Langlands.BruhatTits.IntegralModels.iwahoriOrder F N` is the order `𝔄(𝓛)` of the standard
complete lattice chain in `F^N` (BK93 p. 23). This module does not formalize that relation.
