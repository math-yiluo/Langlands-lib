# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `ClosedLimitGC4`).

- `trans`: the transition map between the base changes to `Spec S'` and `Spec S` for `S ≤ S'`;
  `q_eq_comp_trans`: `q i = q i' ≫ trans` when `S i ≤ S i'`.
- `exists_lift`: a point `z` of the base change to `Spec S` and a point `t` of `Spec A` with the same
  image in `Spec S` come from a point `w` of the base change to `Spec A`
  (`Scheme.Pullback.exists_preimage_pullback`).
- `solution`: a continuous map is closed iff it is specializing (`isClosedMap_iff_specializingMap`).
  Given `x` and a specialization `t'` of its image in `Spec A`, every stage `i` gives a point over
  `t'` in the closed set `C i = (q i)⁻¹ (closure {q i x})`. The fibre over `t'` is compact (it is
  the range of `Scheme.Hom.fiberι`), and the sets `C i` decrease along the directed family, so they
  have a common point `z` in the fibre (`IsCompact.inter_iInter_nonempty`). Finally `z` lies in the
  closure of `x`: otherwise the open complement of `closure {x}` contains some `(q i)⁻¹ W` with
  `z ∈ (q i)⁻¹ W` (`AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra`),
  and `q i z ∈ closure {q i x}` forces `q i x ∈ W`, a contradiction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.ClosedLimitGC4.trans`
- theorem `P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.ClosedLimitGC4.q_eq_comp_trans`
- theorem `P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.ClosedLimitGC4.exists_lift`
- theorem `P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra` (same contribution).
All modules also import `Mathlib`.
