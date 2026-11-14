# NYLL M300.001: finiteness over the absolute base

The theorem
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_finite_over_absoluteBase`
has the complete source telescope and proves the published target:

```lean
theorem finiteAbelianSubextension_finite_over_absoluteBase
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_finite_over_absoluteBaseStatement K L
```

Here the namespace is `Langlands.NYLL.LocalClassFieldTheory`, with
`open ClassFormation`. Both `K` and `L` are explicit, the field instance is
implicit, and `K` lies in universe zero. There are no universe parameters.
The target is the unchanged proposition definition in the sibling
[`Statements.lean`](../Statements.lean):

```lean
Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
  extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
    (le_baseField L.field))
```

For `G = Gal(SeparableClosure K / K)`, this says that the subgroup `L.field`
has finite index in the abstract class-formation base `baseField G`. The
package `L` already supplies finiteness relative to `intrinsicAbstractBase K`,
the closed fixing subgroup of the bottom intermediate field. The theorem
transfers that finiteness to the abstract base. It assumes only `[Field K]`;
there is no local-field, valuation or finite-dimensionality assumption.

The proof uses the finiteness field of the finite abelian subextension
package. Its normality and commutativity fields are not needed.

## Implemented proof and dependencies

The module imports the published target by Lean module name and the published
equality proof
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`.
Its argument is:

1. Specialize `closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)`
   to obtain
   `hbase : intrinsicAbstractBase K = baseField (intrinsicAbsoluteGalois K)`.
   The intrinsic definitions unfold to the bottom fixing subgroup and this
   Galois group, respectively. The separable closure has the required
   algebra and Galois instances from the published imports.
2. Use `change` to unfold the target and the `extensionSubgroup`
   abbreviation. The latter is
   `L.field.toSubgroup.subgroupOf (baseField G).toSubgroup`; its containment
   proof is an unused argument of the abbreviation.
3. Rewrite the abstract base by `rw [← hbase]`. The resulting quotient is
   definitionally the quotient whose finiteness is `L.finite`, so
   `exact L.finite` finishes.

The equality proof is published NYLL M089.001; its implementation uses
Mathlib's `IntermediateField.fixingSubgroup_bot` and closed-subgroup
extensionality. The package projection `L.finite` is the published M296.005
abbreviation. All declarations are imported from the Library by Lean name.
This proof does not use the source's finite-index transitivity theorem
M040.024 or the M299.006 finite-index instance; the equality suffices.
No instance or auxiliary public declaration is introduced.

## Source, attribution and modifications

Adapted by Worker 665 from Naganori Yamaguchi, NYLL ClassFieldTheory,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean),
unit M300.001, lines 34–46. The source context at lines 25–32 and the
adjacent M300.002 proof at lines 48–75 were also read. The latter already
uses the equality of the two base subgroups.

The retained source file is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`;
its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The Library's errata notes contain no NYLL-specific entry.

The modifications are:

- Extract only M300.001 into the focused `AbsoluteBase/U001/Proofs` module
  and prefix the source namespace with `Langlands.NYLL`.
- Write the complete source section telescope explicitly and use the exact
  published Prop target as the conclusion.
- Replace the source's transitivity proof by the equality transport described
  above. This is a new proof of the same proposition.
- Replace the broad source imports by the target module and the equality
  proof module, keep only the used `ClassFormation` opening, and omit the
  unnecessary `noncomputable section`.
- Retain the original theorem docstring, copyright and author header, and
  add a module explanation recording the changed proof.

The original Apache-2.0
[`LICENSE`](../../../../../../../../../licenses/NYLL/LICENSE) and
[`NOTICE`](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.
No external project is installed or copied into the proof's import closure.

## Development verification

The proof compiled in the required environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
Check `35648bf4-f4b2-48d8-9bda-7a60ab04d3c3` compiled the proof with no
errors or warnings. Check `e4561e4d-2b07-44e1-9831-67670f98250f` compiled
the final Lean source and a private signature diagnostic, again without errors
or warnings. The diagnostic assigned the unapplied theorem constant to the
full displayed telescope and printed its universe-zero type. It is excluded
from this contribution.

Declaration inspection reports a theorem with no universe parameters and
only the standard assumptions `propext`, `Classical.choice` and `Quot.sound`.
These development checks are separate from independent semantic review and
the candidate's exact-target and publication checks.
