# Additive self-duality of a p-adic field

Author: Worker 784. This module is an internal prerequisite of the exact proof task
`62de5903-b616-4b5c-88eb-a066b77c5467` (all-character supercuspidal coinvariant finiteness).
It supplies the additive duality that turns an arbitrary nondegenerate upper-unipotent
character into a diagonal conjugate of the standard character.

## Main theorem

`Langlands.HarmonicAnalysis.padicAdditiveSelfDuality p F T` takes every prime `p`, every
`F : PadicField.{u} p` and every supplied `T : F.TopologicalData`, and installs
`T.topology`. Then for every `ψ : UnitaryAdditiveCharacter F.Carrier` (continuous,
nontrivial, unit-circle valued) and every complex additive character
`χ : AddChar F.Carrier ℂ` with `IsLocallyConstant χ`, there exists `a : F.Carrier` with

```text
∀ x, χ x = ψ.complex (a * x)
```

There is no unitarity, nontriviality or continuity assumption on `χ` beyond local
constancy. The trivial character is covered with `a = 0`. The theorem is the
`T`-namespace lemma `exists_eq_complex_mul_of_isLocallyConstant`, restated for all `p`,
`F` and `T`. It does not claim uniqueness of `a`.

## Source

Bernstein–Zelevinsky (1976), §5.3, printed page 44 (source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`). For a fixed nontrivial
additive character `ψ_0`, the map `a ↦ ψ_a = ψ_0(a ·)` identifies `F^k` with its character
group (the source cites Weil, *Basic Number Theory*, Ch. II, §5). This module proves the
case `k = 1` for locally constant complex characters, which is exactly what §5.5 needs:
every additive character is some `ψ_0(a ·)`. The proof route is internal and uses only
finite abelian duality.

## Conventions

`L_j = T.additiveLattice j = {x | v(x) ≤ exp j}`, the fractional ideal `π^(-j) O` of
[`Conductor`](Conductor.md). These lattices increase with `j`. `n = T.additiveConductor ψ`
is the largest level with `ψ` trivial on `L_n`.

## Lattice lemmas

- `mul_mem_additiveLattice_add`: `L_i · L_j ⊆ L_(i+j)`.
- `map_mulLeft_additiveLattice`: for `c ≠ 0`, multiplication by `c` maps `L_j` onto
  `L_(j - ord c)`. This rests on the published `mul_mem_additiveLattice_iff`.
- `isCompact_additiveLattice` and `isOpen_additiveLattice`, reused from
  [PadicLatticeTopology](PadicLatticeTopology.md): every lattice is compact and
  open for `T.topology`. These are Worker 252's original declarations, moved from
  the Rankin–Selberg cutoff module with unchanged statements and proofs.
- `complex_eq_one_of_mem_conductor`: `ψ.complex` is `1` on `L_n`.
- `mem_additiveLattice_of_forall_complex_mul_eq_one`: if `ψ(a x) = 1` for all `x ∈ L_m`,
  then `a ∈ L_(n-m)`. This rests on the published annihilator theorem
  `integer_annihilator_iff_mem_additiveLattice`.

## Characters of quotient groups

`AdditiveSelfDuality.quotientAddChar K φ hφ` descends a complex additive character `φ` of an
additive commutative group, trivial on the subgroup `K`, to the quotient `G ⧸ K`.
`quotientAddChar_mk` is its value on classes.

## Finite levels

`exists_eq_complex_mul_on_additiveLattice ψ χ k M`: if `χ` is trivial on `L_k`, then for
every `M` there is `a` with `χ x = ψ(a x)` for all `x ∈ L_M`. The proof works with two
finite quotient groups:

- `B = L_M / (L_k ∩ L_M)` and `A = L_(n-k) / (L_(n-M) ∩ L_(n-k))`. Both are finite, since an
  open subgroup of a compact group has finite index (Mathlib
  `AddSubgroup.quotient_finite_of_isOpen`).
- For `a ∈ L_(n-k)`, `x ↦ ψ(a x)` on `L_M` is trivial on `L_k`, because
  `L_(n-k) · L_k ⊆ L_n`. It therefore descends to a character of `B`. This character only
  depends on `a` modulo `L_(n-M)`, which gives a map `Φ : A → AddChar B ℂ`.
- `Φ` is injective, by the annihilator lemma.
- `A` and `B` have the same cardinality. Multiplication by `π^(M+k-n)` carries `L_k` and
  `L_M` onto `L_(n-M)` and `L_(n-k)`, and Mathlib's `AddSubgroup.relIndex_map_map_of_injective`
  preserves relative indices.
- Mathlib's `AddChar.card_eq` says that a finite abelian group has as many complex characters
  as elements. So `Φ` is bijective, and the descended restriction of `χ` is some `Φ(a)`.

## Passage to the limit

`exists_eq_complex_mul_of_isLocallyConstant` proves the main theorem.

- Local constancy makes `{χ = 1}` an open neighbourhood of `0`. By the published
  `exists_additiveLattice_subset`, it contains a lattice `L_k`.
- For `j : ℕ`, let `S_j` be the set of `a` with `χ = ψ(a ·)` on `L_(k+j)`. These sets
  decrease, are nonempty by the finite levels, and are closed by continuity of `ψ`. `S_0`
  lies in the compact `L_(n-k)` by the annihilator lemma.
- Mathlib's `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` gives a point
  `a` in every `S_j`. Every `x` lies in some `L_(k+j)`, so `χ x = ψ(a x)`.

## Dependencies

The module imports the published `PadicAdditiveConductorProof` and
`PadicScalarHaarScalingProof`, and the shared `PadicLatticeTopology`, together with Mathlib's finite Pontryagin duality and open
subgroups. It does not depend on representation theory, Whittaker models, derivatives,
segments or any statement excluded by the parent task.
