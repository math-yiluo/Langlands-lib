# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact`. Statement. `LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact`: let `f : C → D` be a
surjective map of cochain complexes of `R`-modules (indexed by `ℕ`) whose kernel complex is acyclic. Then `f`
induces isomorphisms `H⁰(C) ≅ H⁰(D)` and `Hⁿ⁺¹(C) ≅ Hⁿ⁺¹(D)`, compatible with `f` on representatives.

Proof. Direct diagram chase: `f` maps cocycles to cocycles and coboundaries to coboundaries (`map_mem_ker`, `kerMap`,
`bd_le_comap`, `quotMap`). Injectivity and surjectivity of the induced maps (`kerMap_zero_bijective`,
`quotMap_bijective`) use the surjectivity of `f` and the acyclicity hypotheses for the kernel.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.map_mem_ker`
- def `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.kerMap`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.kerMap_apply`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.kerMap_zero_bijective`
- abbrev `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.bd`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.bd_le_comap`
- def `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.quotMap`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.quotMap_mk`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.quotMap_bijective`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.P2mAcyclicKer.main`
- theorem `P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
