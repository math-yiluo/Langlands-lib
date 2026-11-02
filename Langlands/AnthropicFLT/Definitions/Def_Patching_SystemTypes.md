# `Langlands.AnthropicFLT.Definitions.Def_Patching_SystemTypes`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Patching_SystemTypes.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Basic notions for FLT's patching argument.

- `IsLocalRing.IsAdicTopology R`: the topology of a local topological ring is the `𝔪`-adic one.
- `Algebra.TopologicallyFG R S`: `S` has a dense finitely generated `R`-subalgebra; an
  anonymous instance (priority 100) derives it from `Algebra.FiniteType R S`.
- `Module.depth R M` for a local ring `R`: the supremum in `ℕ∞` of the lengths of weakly regular
  sequences on `M` with all elements in the maximal ideal.
- `Algebra.UniformlyBoundedRank`, `Module.UniformlyBoundedRank` and `IsPatchingSystem`: uniform
  bounds on the sizes `#(R i ⧸ 𝔪^k)` and on ranks of modules over their annihilator quotients, and
  the condition that the annihilators of `M i` eventually lie in every open ideal along a filter.

## Declarations

Names, namespaces and statements are the FLT ones.

- class `IsLocalRing.IsAdicTopology`
- class `Algebra.TopologicallyFG`
- anonymous instance (priority 100) of `Algebra.TopologicallyFG R S` from `Algebra.FiniteType R S`
- def `Module.depth`
- class `Algebra.UniformlyBoundedRank`
- class `Module.UniformlyBoundedRank`
- class `IsPatchingSystem`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`, `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, `Mathlib.RingTheory.FiniteType`, `Mathlib.Topology.Algebra.Ring.Basic`, `Mathlib.RingTheory.Regular.RegularSequence`, `Mathlib.Algebra.Module.Torsion.Basic`, `Mathlib.LinearAlgebra.Dimension.Finrank`, `Mathlib.Order.Filter.Ultrafilter.Defs`, `Mathlib.Data.ENat.Lattice`.
