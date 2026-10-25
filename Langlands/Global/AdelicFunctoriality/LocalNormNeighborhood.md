# Local norm groups are neighborhoods of one

Author: Worker 269.

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves that the image of the
actual local norm on unit groups contains a neighborhood of `1`. This holds at every finite
and every infinite place of an arbitrary extension of number fields `L/K`. No Galois, cyclic
or ramification hypothesis is needed. The local norms are `FiniteExtension.localNorm p q` and
`InfiniteExtension.localNorm p q` of [Extension](Extension.md): the determinant norm of the
completed extension `L_q / K_p` built from the actual completion embedding. The topologies are
the existing ones on `p.adicCompletion K` and `p.Completion`, and the topology on units is
Mathlib's units topology. This module changes none of the imported definitions and declares no
global instances.

## Statements

Universes are independent: `K : Type u`, `L : Type v`, `[Field K] [Field L] [Algebra K L]`.

- `RangeMemNhdsOne f`, for a monoid homomorphism `f : M →* Fˣ`, is the proposition
  `Set.range f ∈ 𝓝 (1 : Fˣ)`. It is a name only. `RangeMemNhdsOne.isOpen_range` shows that
  when `M` is a group and multiplication on `F` is continuous, such an `f` has open image. The
  reason is that `Set.range f` is the subgroup `f.range`, and a subgroup that is a neighborhood
  of one point is open (`Subgroup.isOpen_of_mem_nhds`).
- `range_pow_mem_nhds_one (hn : n ≠ 0)`: in a complete nontrivially normed field `F` of
  characteristic zero, the set of `n`-th powers `x ^ n` of units `x : Fˣ` is a neighborhood of
  `1` in `Fˣ`.
- `range_finiteLocalNorm_mem_nhds p q`: assume `[NumberField K] [NumberField L]`. Let
  `p : HeightOneSpectrum (𝓞 K)` and `q : HeightOneSpectrum (𝓞 L)` with
  `[q.asIdeal.LiesOver p.asIdeal]`. Then
  `Set.range (Units.map (FiniteExtension.localNorm p q)) ∈ 𝓝 (1 : (p.adicCompletion K)ˣ)`.
- `range_infiniteLocalNorm_mem_nhds p q`: assume `[NumberField K]`. Let `p : InfinitePlace K`
  and `q : InfinitePlace L` with `[q.LiesOver p]`. Then
  `Set.range (Units.map (InfiniteExtension.localNorm p q)) ∈ 𝓝 (1 : p.Completionˣ)`.
  `NumberField L` is not needed here. Classically, at a real place below a complex place the
  norm is `z ↦ |z| ^ 2`, which is not onto the real units. The theorem claims only that the
  image contains a neighborhood of `1`.
- `isOpen_range_finiteLocalNorm p q` and `isOpen_range_infiniteLocalNorm p q`, under the same
  hypotheses: the local norm groups `Set.range (Units.map (localNorm p q))` are open in the
  base unit group.

## Proofs

`range_pow_mem_nhds_one`: the map `x ↦ x ^ n` has strict derivative `n * 1 ^ (n - 1) = n` at
`1` (`hasStrictDerivAt_pow`). This is nonzero because `n ≠ 0` and `F` has characteristic zero.
The one-variable inverse function theorem `HasStrictDerivAt.map_nhds_eq` needs `F` complete.
It gives `map (· ^ n) (𝓝 1) = 𝓝 1`, so the image of the open neighborhood `{x | x ≠ 0}` of `1`
is a neighborhood of `1` in `F`. Its preimage under the continuous map `Units.val` is a
neighborhood of `1` in `Fˣ`. A unit `u` in that preimage is `x ^ n` with `x ≠ 0`, so
`u = (Units.mk0 x hx) ^ n`.

Finite places: inside the proof, `p.adicCompletion K` gets the nontrivially normed field
structure `Valued.toNontriviallyNormedField` of its rank-one valuation. This structure extends
the same `Valued.toNormedField` that Mathlib installs as its normed field instance, so its
topology is the existing one. Lean checks that the statement, which uses the existing
topology, matches the generic lemma by definitional unfolding. The completion is complete
(Mathlib's `CompleteSpace` instance). It has characteristic zero because
`algebraMap K (p.adicCompletion K)` is injective (`charZero_of_injective_algebraMap`). The
local degree `d = finrank (p.adicCompletion K) (q.adicCompletion L)` is positive
(`Module.finrank_pos`, using the finiteness instance from [Extension](Extension.md)). For a
unit `x` of `K_p`, `FiniteExtension.localNorm_algebraMap` gives
`localNorm p q (completionMap p q x) = x ^ d`. So every `d`-th power of a unit is a norm of a
unit, and the neighborhood from `range_pow_mem_nhds_one` lies in the norm image.

Infinite places: the same argument. The nontrivially normed field structure on `p.Completion`
is built from its existing normed field instance, with the witness `‖2‖ = 2 > 1` obtained
through the isometric embedding `InfinitePlace.Completion.extensionEmbedding` into `ℂ`. This
is the same construction as the local instance in [Extension](Extension.md). Completeness is
Mathlib's instance, and characteristic zero again comes from the injective `algebraMap K`.
`InfiniteExtension.localNorm_algebraMap` gives the `d`-th power formula for
`NumberField.LiesOver.completionMap`.

## Provenance

Derived. Artin and Tate, *Class Field Theory* (2009), Chapter V, Section 4, proof of
Theorem 2 (printed p.17, PDF p.26), uses this local fact: an idele "so close to 1 at all
p ∈ S" is a local norm at those places. The appended errata (PDF p.202) do not change this
passage. The book does not prove the fact at that point. The proof here is the elementary one
described in the task context of 6baf00a9: an inverse function theorem for `n`-th powers, plus
the local norm of a base scalar being its local-degree power. It does not use local class
field theory. `RangeMemNhdsOne`, the generic power lemma and the openness corollaries are
internal packaging. The two neighborhood statements are in the exact shape Worker 226
requested for the local adjustment step of the almost-everywhere-split norm theorem (task
275d5e34).
