# Joint injectivity of restriction to two generating normal fields

This module proves
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_prod_injective_of_sup_eq_topStatement`
under the theorem name
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_prod_injective_of_sup_eq_top`.
It imports the published [statement module](Statements.lean) and leaves its
Lean and Markdown unchanged.

## Exact scope

The theorem has the published proposition itself as its type, with independent
universe parameters `u` and `v`. Its quantified data are an explicit field
`K : Type u`, an implicit field `P : Type v`, `[Algebra K P]`, two explicit
intermediate fields `E₁ E₂ : IntermediateField K P`, instances
`[Normal K E₁]` and `[Normal K E₂]`, and the explicit equality
`hsup : E₁ ⊔ E₂ = ⊤`, in the target's original order and binder kinds.
It proves injectivity of the product of the two `AlgEquiv.restrictNormalHom`
maps on `P ≃ₐ[K] P`. It adds no hypotheses.

## Implemented proof

After introducing the target's quantifiers, `injective_iff_map_eq_one` reduces
injectivity of the product homomorphism to showing that every element of its
kernel is the identity. Suppose `sigma` maps to the identity pair. Applying
`congrArg Prod.fst` and `congrArg Prod.snd` shows that both restrictions of
`sigma` are identities.

For each `Eᵢ`, `MonoidHom.mem_ker` places `sigma` in the restriction kernel,
and `IntermediateField.restrictNormalHom_ker` identifies that kernel with
`Eᵢ.fixingSubgroup`. The two memberships combine using
`IntermediateField.fixingSubgroup_sup`, so `sigma` fixes `E₁ ⊔ E₂`.
Rewriting by `hsup` and `IntermediateField.fixingSubgroup_top` places `sigma`
in the bottom subgroup of `P ≃ₐ[K] P`; its membership is definitionally
`sigma = 1`. This completes the kernel criterion.

These Mathlib facts apply to the target's arbitrary field extension. The
normality instances supply the restriction homomorphisms and their kernel
identifications.

## Source and modifications

The proof is adapted from Naganori Yamaguchi's `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean`,
unit M331.001: docstring lines 28–29, statement lines 30–35, and proof lines
36–52. The [retained original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean>)
was read in full; its SHA-256 is
`49dbe156918022358d4a244d2de1b16d00e4c6b0a43249bfd6ac6f77ef35318c`.
The source registrations are
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The public [port inventory](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m331)
records M331.001 and has no patch10 change for this module. No applicable
NYLL erratum was found in the current Library's `notes/errata/`.

Worker 307 made these adaptations on 14 November 2026:

- Retained the original copyright, license, author header, declaration
  docstring, and complete proof body.
- Prefixed the namespace with `Langlands.NYLL` and retained the theorem's
  source name.
- Replaced the source imports with the published `CompositumRestriction.Statements`
  import, which supplies the exact target and its Mathlib dependencies.
- Gave the theorem the closed proposition target as its type, explicitly
  retained its independent universe parameters, and introduced its quantifiers
  before the source proof.
- Extracted only M331.001 into this dedicated module, omitting the other source
  declarations, unused namespace openings, and unnecessary `noncomputable section`.

The check environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The original project targeted Lean 4.35.0-rc2 with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and license

Original author: Naganori Yamaguchi (assisted by OpenAI Codex), copyright 2026.
The Apache-2.0 source header is retained verbatim. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged; their
SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
