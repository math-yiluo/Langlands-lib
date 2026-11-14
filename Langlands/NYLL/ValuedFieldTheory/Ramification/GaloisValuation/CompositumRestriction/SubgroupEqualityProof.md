# Subgroup equality from two images

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.subgroup_eq_of_prod_map_injective_of_left_maps_eq_botStatement`
under the exact theorem name
`Langlands.NYLL.LocalClassFieldTheory.subgroup_eq_of_prod_map_injective_of_left_maps_eq_bot`.
It imports the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.Statements`
module and changes neither that module nor its dependencies.

## Scope

For arbitrary groups `G : Type uG`, `G₁ : Type uG₁`, `G₂ : Type uG₂`,
homomorphisms `f₁ : G →* G₁`, `f₂ : G →* G₂`, and an injective product
`f₁.prod f₂`, the theorem identifies subgroups `A` and `B` whose `f₁` images
are both bottom and whose `f₂` images agree. The theorem's type is the exact
closed published proposition at the three independent universe parameters
`uG`, `uG₁`, `uG₂`. Its implicit group binders, instance binders, explicit
homomorphisms and hypothesis order are inherited unchanged by unfolding the
target. There are no commutativity, normality, finiteness, field or valuation
hypotheses.

## Implemented proof

The proof follows the pinned original's local inclusion argument. For subgroups
`C` and `D` satisfying the three image hypotheses, take `x ∈ C`. Since their
right images agree, the witness `x` gives `f₂ x ∈ D.map f₂`; unpacking this
membership supplies `y ∈ D` with `f₂ y = f₂ x`. The witnesses `x` and `y`
likewise put their left images in `C.map f₁` and `D.map f₁`. Rewriting these
subgroups to bottom and applying `Subgroup.mem_bot.mp` gives `f₁ x = 1` and
`f₁ y = 1`. `Prod.ext` now proves equality of the two product images, so the
assumed injectivity gives `x = y`. Transporting `y ∈ D` yields `x ∈ D`.
Finally `le_antisymm` applies this inclusion argument in both orders, using
the symmetry of the right-image equality for the second order.

Only the imported group and subgroup API is used. Neither of the two other
M331 restriction-injectivity proofs is an input to this proof.

## Source reuse and modifications

Original author: Naganori Yamaguchi (assisted by OpenAI Codex), copyright 2026.
The source is `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean`.
The [retained original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean>)
has SHA-256
`49dbe156918022358d4a244d2de1b16d00e4c6b0a43249bfd6ac6f77ef35318c`.
M331.003 occupies docstring lines 149–150, statement lines 151–158 and proof
lines 159–182; these passages and the original module header were read.
The existing registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The public partition is [M331](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m331).
No patch10 compatibility change applies to this source module, and no
applicable NYLL erratum was found in the current Library's `notes/errata/`.

Worker 242 retains the original copyright, Apache-2.0 and author header verbatim,
prefixes the namespace with `Langlands.NYLL`, and reuses the original proof body
after introducing the parameters of the published closed proposition. The
original explicit theorem binders are represented by this exact target rather
than restated separately. Three independent universes are explicitly named.
The direct import is replaced by the published target module; the original
unrelated field proofs, section variables, namespace openings and unnecessary
`noncomputable section` are omitted. A module description and dated modification
notice are added. There are no other proof changes.

The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

## Environment

The required environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream targeted Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation and declaration
inspection succeeded with zero errors and zero warnings. Inspection retained
`uG`, `uG₁`, `uG₂` as separate level parameters and reported only `propext`
and `Quot.sound` as assumptions. Development checking and formal acceptance
are separate; independent review and exact-target machine validation are
required for publication.
