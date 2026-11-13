# Restriction from a compositum: proposition targets

This module defines three closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, extracted from Naganori Yamaguchi's
`ClassFieldTheory`. They specify joint injectivity of field restriction and
the associated subgroup equality criterion. They are statement targets; this
module supplies no proofs of the three propositions.

## Original source

The pinned source is `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean`.
The [retained source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean>)
was read in full, including the proof bodies. Its SHA-256 is
`49dbe156918022358d4a244d2de1b16d00e4c6b0a43249bfd6ac6f77ef35318c`.

The source registrations are:

| Literature registration | Content fingerprint |
| --- | --- |
| `external-lean-reuse-snapshots-2026-10-21` | `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01` |
| `nyll-classfieldtheory-fbd320cd-supplement` | `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330` |

The inventory is
[`notes/reuse/nyll-public-port/m313-m336.md`, M331](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m331).
No patch10 change applies to this module, and no applicable NYLL erratum was
found in the current Library's `notes/errata/`.

## Source correspondence

All adapted names below have the prefix
`Langlands.NYLL.LocalClassFieldTheory.`; all original names have the prefix
`LocalClassFieldTheory.`.

| Unit | Original declaration | Adapted proposition | Exact source passage |
| --- | --- | --- | --- |
| M331.001 | `restrictNormalHom_prod_injective_of_sup_eq_top` | `restrictNormalHom_prod_injective_of_sup_eq_topStatement` | Docstring 28–29; statement 30–35; proof 36–52 |
| M331.002 | `intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq` | `intermediateFieldRestrictNormalHom_prod_injective_of_sup_eqStatement` | Docstring 56–58; statement 59–69; proof 70–147 |
| M331.003 | `subgroup_eq_of_prod_map_injective_of_left_maps_eq_bot` | `subgroup_eq_of_prod_map_injective_of_left_maps_eq_botStatement` | Docstring 149–150; statement 151–158; proof 159–182 |

The source section declares `universe u v` at line 24, the field variables
at line 26, and `universe w` at line 54. The complete file has 184 lines.
Task 6045's broad locators 30–53 and 151–187 cover the first and third units;
line 53 is blank and the third unit's proof ends at 182.

### M331.001: restriction from the ambient field

For an explicit `K : Type u`, an implicit `P : Type v`, supplied `[Field K]`,
`[Field P]`, and `[Algebra K P]`, take explicit intermediate fields
`E₁ E₂ : IntermediateField K P` and instances `[Normal K E₁]`,
`[Normal K E₂]`. The final explicit premise is `hsup : E₁ ⊔ E₂ = ⊤`.
The conclusion is exactly `Function.Injective` of the product of the two
`AlgEquiv.restrictNormalHom` homomorphisms from `P ≃ₐ[K] P` to
`(E₁ ≃ₐ[K] E₁) × (E₂ ≃ₐ[K] E₂)`.

The universes `u` and `v` remain independent. There is no finite-dimensionality,
separability, valuation, topology or local-field premise. Normality is assumed
only for the two intermediate fields. The source proof uses the two restriction
kernels, the fixing subgroup of a supremum, and the trivial fixing subgroup of
top. Those facts explain the statement's meaning; they are not extra premises
of this target.

### M331.002: restriction from a generated intermediate field

For explicit `K : Type u` with `[Field K]` and implicit `Omega : Type w`
with `[Field Omega]` and `[Algebra K Omega]`, take explicit
`E₁ E₂ F : IntermediateField K Omega`, explicit inclusions
`hE₁ : E₁ ≤ F` and `hE₂ : E₂ ≤ F`, the normality instances
`[Normal K E₁]` and `[Normal K E₂]`, and explicit
`hsup : E₁ ⊔ E₂ = F`, in this order. The conclusion is injectivity of the
product of the two published maps
`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom Eᵢ F hEᵢ`.
Their exact types are
`(F ≃ₐ[K] F) →* (Eᵢ ≃ₐ[K] Eᵢ)`. The source's explicit type annotations on
these maps are retained.

The universes `u` and `w` remain independent. The unused source section
variables `P`, `[Field P]`, and `[Algebra K P]` are not parameters of the
original theorem and are not quantified by this proposition. No normality of
`F` or `Omega`, finiteness, separability or local-field premise is added.
The maps use the inclusion-induced algebra and scalar-tower structures
encapsulated in the published definition; no alternative `Algebra Eᵢ F`
is supplied as an extra parameter.

The source proof restricts `E₁` and `E₂` inside `F`, applies M331.001, and
uses the evaluation formula M259.002 to compare restrictions. This statement
only needs M259.001, the definition of the maps. It imports neither the
evaluation statement nor its proof and assumes neither as a hypothesis.

### M331.003: subgroup equality from two images

The implicit groups have independent universes:
`{G : Type uG} {G₁ : Type uG₁} {G₂ : Type uG₂}`, with
`[Group G] [Group G₁] [Group G₂]`. This explicitly names the three independent
universes expressed by the source's `{G G₁ G₂ : Type*}`. There are no inherited
field parameters.

The remaining explicit binders retain source order and kinds:
`f₁ : G →* G₁`, `f₂ : G →* G₂`,
`hinjective : Function.Injective (f₁.prod f₂)`,
`A B : Subgroup G`, `hA₁ : A.map f₁ = ⊥`,
`hB₁ : B.map f₁ = ⊥`, and `h₂ : A.map f₂ = B.map f₂`.
The conclusion is `A = B`. There is no commutativity, finiteness,
normal-subgroup or surjectivity premise. The source proof proves both
inclusions by finding an element with equal right image and using trivial
left images plus joint injectivity to identify the elements. This explains
the criterion without adding any proof as an input.

## Imports and complete modification record

The adapted module directly imports:

- `Mathlib.FieldTheory.Galois.Basic`, unchanged from source. It supplies the
  field, algebra, intermediate-field, normality, restriction and group
  interfaces used here.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions`,
  replacing the source import
  `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction`.
  This published M259.001 module supplies
  `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom`.

All three targets are grouped in the proposed `CompositumRestriction.Statements`
module under `Langlands/NYLL/`. The adaptation:

1. Retains the original copyright, license and author header verbatim and
   adds Worker 314's dated modification notice.
2. Prefixes the enclosing namespace with `Langlands.NYLL`.
3. Replaces `open RamificationTheory` by
   `open Langlands.NYLL.RamificationTheory` and omits the redundant
   `open LocalClassFieldTheory` inside its own namespace.
4. Retains the Mathlib import and substitutes the published adapted definition
   import for the external NYLL import, as listed above.
5. Changes each `theorem` into a `def` with the original name followed by
   `Statement`. All term binders become quantifiers inside a closed `: Prop`
   definition. Their order, explicit/implicit/instance kinds, hypotheses,
   restriction expressions and conclusions are preserved.
6. Moves the used section variables into these quantifiers, preserving the
   two independent field universes in each field statement and avoiding unused
   section variables. Names the third statement's three implicit universes
   `uG`, `uG₁`, `uG₂`; this changes no universe constraint.
7. Retains the three declaration docstrings verbatim, replaces the module
   documentation with a description of the proposition targets, and omits
   all original proof bodies and the unnecessary `noncomputable section`.
8. Sets `linter.unusedVariables` to `false` to retain the source names of
   proposition hypotheses whose proof terms are unused in the conclusions.
   This only suppresses lint warnings; it changes no proposition.

No other source declarations are present in the original file, and no new
mathematical proof or data definition is introduced. These propositions do
not assert that their proofs have been ported. M332 base change and any
comparison with an Artin map remain outside this unit.

## Environment and intended use

The required check environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream targeted Lean 4.35.0-rc2 with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The entry declaration is
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_prod_injective_of_sup_eq_topStatement`;
the other two full names are obtained from the correspondence table with
the same namespace prefix. Each is a separate closed, universe-polymorphic
proposition suitable as the exact target of a later proof.

Development checks of this exact Lean source succeeded with zero errors and
zero warnings. Each declaration was individually inspected with `lean_check`
and returned `statement_returns_prop = true`. The inspected universe parameters
were `u, v` for M331.001, `u, w` for M331.002 and `uG, uG₁, uG₂` for
M331.003. Inspection reported only the standard assumptions `propext`,
`Classical.choice`, `Quot.sound` for the field statements and `propext`,
`Quot.sound` for the group statement. These development results do not
constitute independent mathematical acceptance.

## Attribution and license

Original author: Naganori Yamaguchi (assisted by OpenAI Codex), copyright 2026.
The Apache-2.0 header is retained unchanged. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 314 extracted these statements from the pinned original and reused
Worker 30's published M259.001 definition by import.
