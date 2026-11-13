# The intrinsic abstract base and the absolute Galois group

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`
(file SHA-256 `307ae64486245113f5aa94505bbc184048f4daec1af85f89f94f965c57b25e5a`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M091.004 | `intrinsicAbstractBaseEquivAbsolute` (47–56) | `intrinsicAbstractBaseEquivAbsolute` |

The original name is in `LocalClassFieldTheory`; the adapted name is
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBaseEquivAbsolute`.

## Content

For a field `F : Type`, `intrinsicAbstractBaseEquivAbsolute F` is a
multiplicative equivalence from the underlying subgroup of
`intrinsicAbstractBase F` to `intrinsicAbsoluteGalois F`.
`intrinsicAbstractBase F` is the closed fixing subgroup of the bottom
intermediate field of `SeparableClosure F` over `F`.
`intrinsicAbsoluteGalois F` is `Gal(SeparableClosure F / F)`.
Both are published (M091.003 and M091.001) in
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`.
The equivalence is Mathlib's `MulEquiv.subgroupCongr`, applied to the equality
`(intrinsicAbstractBase F).toSubgroup = ⊤`, followed by `Subgroup.topEquiv`.
So it sends an element `σ` of the subgroup to its underlying automorphism
`σ.1`, by definition, and its inverse sends `σ` to `⟨σ, _⟩`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The module is placed in a separate `U004/Definitions` file.
- The source imports the broad module `GaloisExtensionQuotient`. The port
  imports only the published module that supplies `intrinsicAbstractBase` and
  `intrinsicAbsoluteGalois`. The source openings
  `RamificationTheory CyclicCohomology KummerTheory ClassFormation` are unused
  here and are omitted.
- The `noncomputable` modifier, the docstring, the explicit `Type`-zero field
  parameter, the result type and the data of the body
  (`(MulEquiv.subgroupCongr _).trans Subgroup.topEquiv`) are unchanged.
- **Proof of the subgroup equality inside the body.** The source proves
  `(intrinsicAbstractBase F).toSubgroup = ⊤` by
  `rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField, baseField_toSubgroup]`.
  The theorem `closedFixingSubgroup_bot_eq_baseField` is source unit M089.001.
  At Library commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e` it is published
  only as the proposition
  `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseFieldStatement`
  (in `GaloisExtensionQuotient/Initial/Statements`), without a proof. The port
  therefore proves the same equality another way. It unfolds the goal with
  `change` to `(⊥ : IntermediateField F (SeparableClosure F)).fixingSubgroup = ⊤`
  and closes it with Mathlib's `IntermediateField.fixingSubgroup_bot`. The
  equality is a proposition, so the definition does not depend on which proof
  is used. A private check, which is not part of the candidate, confirms by
  `rfl` that the source rewrite chain gives this same equivalence. In that
  check the chain takes the M089.001 proposition as a hypothesis and uses the
  published `Langlands.NYLL.ClassFormation.baseField_toSubgroup` (M010.004).
  The check also confirms that the forward map is `σ ↦ σ.1` by `rfl` and that
  the source proof of M091.005 goes through.
- The source simp lemma `intrinsicAbstractBaseEquivAbsolute_symm_apply_val`
  (M091.005, lines 58–64) is a theorem and is not part of this definition unit.

## Library and Mathlib comparison

No Library declaration has this type. In Library `.lean` files,
`intrinsicAbstractBase` and `intrinsicAbsoluteGalois` occur only in their
defining module and in the abbreviations
`Langlands.NYLL.PortInternal.M097.d001`/`d003`, which restate them. Mathlib's
`IntermediateField.fixingSubgroupEquiv ⊥` has a different codomain: the
automorphisms of `SeparableClosure F` over the intermediate field `⊥`, a type
different from `Gal(SeparableClosure F / F)`. Library files write the pattern
`(MulEquiv.subgroupCongr h).trans Subgroup.topEquiv` inline for other subgroups
(for example `Langlands/Weil/Local/ExtensionWeilEquiv.lean`). They do not
provide it as a reusable declaration for this subgroup.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
