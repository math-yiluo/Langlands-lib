# NYLL M113.013, M113.018, M113.021–M113.023, M113.028–M113.035, M113.056, M113.057 and M113.059–M113.065: norm and `σ - 1` homomorphisms, norm and augmentation subgroups, low-degree Herbrand quotient groups

## Source

The paired Lean file extracts twenty-two declarations from Naganori Yamaguchi's
ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` (1717
lines, SHA-256
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M113 (patch status "none in patch10"). The whole source file was read,
including its section context (lines 24–33), its only `variable` commands
(lines 62–64) and every `omit … in` preceding an extracted declaration. The
file has no other `variable`, `section`, `include` or `open` command before
its closing lines 1713–1717.

All original names are in `CyclicCohomology.ProfiniteCohomology.Herbrand`; all
adapted names are the same names in
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.

| Unit | Source declaration; kind and header line(s); `omit` / docstring / end lines | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M113.013 | `tateNormHom`; `def`, 186; 183–184 / 185 / 189 | `tateNormHom` (line 43) |
| M113.018 | `sigmaMinusOneHom`; `def`, 222; 219–220 / 221 / 225 | `sigmaMinusOneHom` (line 50) |
| M113.021 | `tateNormSubgroup`; `def`, 252–253; none / 251 / 254 | `tateNormSubgroup` (line 57) |
| M113.022 | `normKernelSubgroup`; `def`, 257–258; none / 256 / 259 | `normKernelSubgroup` (line 62) |
| M113.023 | `augmentationSubgroup`; `def`, 262–263; none / 261 / 264 | `augmentationSubgroup` (line 67) |
| M113.028 | `HerbrandH0`; `def`, 316–317; none / 315 / 318 | `HerbrandH0` (line 72) |
| M113.029 | `HerbrandHMinusOne`; `def`, 322–323; none / 320–321 / 324 | `HerbrandHMinusOne` (line 78) |
| M113.030 | `herbrandH0CommGroup`; `instance`, 329; 326–327 / 328 / 331 | `herbrandH0CommGroup` (line 83) |
| M113.031 | `herbrandHMinusOneCommGroup`; `instance`, 336–337; 333–334 / 335 / 339 | `herbrandHMinusOneCommGroup` (line 89) |
| M113.032 | `HerbrandH0.equiv`; `def`, 345–348; 341–342 / 343–344 / 354 | `HerbrandH0.equiv` (line 97) |
| M113.033 | `HerbrandHMinusOne.equiv`; `def`, 360–363; 356–357 / 358–359 / 369 | `HerbrandHMinusOne.equiv` (line 111) |
| M113.034 | `HerbrandH0.mk`; `def`, 374; 371–372 / 373 / 377 | `HerbrandH0.mk` (line 124) |
| M113.035 | `HerbrandHMinusOne.mk`; `def`, 382–383; 379–380 / 381 / 386 | `HerbrandHMinusOne.mk` (line 131) |
| M113.056 | `herbrandH0FiniteOfFinite`; `noncomputable instance`, 684–685; 681–682 / 683 / 689 | `herbrandH0FiniteOfFinite` (line 139) |
| M113.057 | `herbrandHMinusOneFiniteOfFinite`; `noncomputable instance`, 694–695; 691–692 / 693 / 699 | `herbrandHMinusOneFiniteOfFinite` (line 148) |
| M113.059 | `rightRegularFunctionTateNormSubgroup`; `abbrev`, 713; 709–711 / 712 / 715 | `rightRegularFunctionTateNormSubgroup` (line 157) |
| M113.060 | `rightRegularFunctionHerbrandH0`; `def`, 721; 717–719 / 720 / 723 | `rightRegularFunctionHerbrandH0` (line 163) |
| M113.061 | `rightRegularFunctionHerbrandH0CommGroup`; `noncomputable instance`, 729–730; 725–727 / 728 / 733 | `rightRegularFunctionHerbrandH0CommGroup` (line 169) |
| M113.062 | `rightRegularFunctionNormKernelSubgroup`; `abbrev`, 739; 735–737 / 738 / 741 | `rightRegularFunctionNormKernelSubgroup` (line 177) |
| M113.063 | `rightRegularFunctionAugmentationSubgroup`; `abbrev`, 747; 743–745 / 746 / 749 | `rightRegularFunctionAugmentationSubgroup` (line 183) |
| M113.064 | `rightRegularFunctionHerbrandHMinusOne`; `def`, 755; 751–753 / 754 / 757 | `rightRegularFunctionHerbrandHMinusOne` (line 189) |
| M113.065 | `rightRegularFunctionHerbrandHMinusOneCommGroup`; `noncomputable instance`, 763–765; 759–761 / 762 / 768 | `rightRegularFunctionHerbrandHMinusOneCommGroup` (line 195) |

The section context is source lines 24–33: `namespace CyclicCohomology`,
`noncomputable section`, `open scoped BigOperators`,
`namespace ProfiniteCohomology`, `namespace Herbrand` and
`universe uG uA uB uC`. The adapted file reproduces it inside
`namespace Langlands.NYLL.CyclicCohomology` and closes it as at source lines
1713–1717.

## The declarations

In this section *finite core* abbreviates the binders
`{G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]`,
*core* is the same without `[Fintype G]`, and *finite rr* abbreviates
`{G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]`. The Lean
file spells out every binder. `tateNorm`, `sigmaMinusOne`, `fixedSubgroup`
(M113.001–M113.003) and `rightRegularFunctionMulDistribMulAction` (M113.009)
are the published constructions of the sibling module `Basic.Definitions`:
`tateNorm G A a = ∏ g : G, g • a`, `sigmaMinusOne G A σ a = σ • a * a⁻¹`,
`fixedSubgroup G A = A^G`, and the right-regular action
`(g • f) x = f (x * g)` on `G → B`. No declaration here assumes that `G` is
cyclic or that `σ` generates `G`.

**`tateNormHom`** (M113.013). Telescope: finite core. Type `A →* A`. Fields:
`toFun := tateNorm G A`, `map_one' := tateNorm_one (G := G) (A := A)` and
`map_mul' := tateNorm_mul (G := G) (A := A)`. It is the norm map `N_G` as a
group endomorphism of `A`.

**`sigmaMinusOneHom`** (M113.018). Telescope: core, then `(σ : G)`. Type
`A →* A`. Fields: `toFun := sigmaMinusOne G A σ`,
`map_one' := by simp [sigmaMinusOne, MulDistribMulAction.smul_one]` and
`map_mul' := sigmaMinusOne_mul (G := G) (A := A) σ`. It is the endomorphism
`a ↦ a^(σ-1) = σ • a * a⁻¹`.

**`tateNormSubgroup`**, **`normKernelSubgroup`** (M113.021, M113.022).
Telescope: explicit `(G : Type uG) (A : Type uA)`, then `[Group G]`,
`[Fintype G]`, `[CommGroup A]`, `[MulDistribMulAction G A]`, as written in the
source (these declarations take their own binders, not the section
variables). Values `MonoidHom.range tateNormHom` (the norm group `N_G A`) and
`MonoidHom.ker tateNormHom` (the norm kernel `{a | N_G a = 1}`).

**`augmentationSubgroup`** (M113.023). Telescope: explicit `(G : Type uG)`,
`(A : Type uA)`, `[Group G]`, `[CommGroup A]`, `[MulDistribMulAction G A]`,
explicit `(σ : G)`; no finiteness of `G`. Value
`MonoidHom.range (sigmaMinusOneHom σ)`, the image `(σ - 1)A` of the single map
`a ↦ σ • a * a⁻¹`. The source docstring calls it "the augmentation image
`I_G A` for a chosen `σ`". It equals the subgroup `I_G A` generated by all
`g • a * a⁻¹` when `σ` generates `G`, but the definition has no generation
hypothesis; for other `σ` it is in general smaller.

**`HerbrandH0`** (M113.028). Telescope as for M113.021. Type `Type uA`. Value
`fixedSubgroup G A ⧸ (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)`:
the quotient of `A^G` by the preimage of `N_G A` under the inclusion
`A^G → A`. Because `N_G A ⊆ A^G` (the target M113.069 in `Statements.lean`
beside this file, not proved here), this is the multiplicative Tate group
`Ĥ⁰(G, A) = A^G / N_G A`.

**`HerbrandHMinusOne`** (M113.029). Telescope as for M113.021, then
`(σ : G)`. Type `Type uA`. Value
`normKernelSubgroup G A ⧸ (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)`,
the quotient of the norm kernel by its intersection with `(σ - 1)A`. When `σ`
generates `G` this is `Ĥ⁻¹(G, A) = ker N_G / I_G A` (using M113.067,
`(σ - 1)A ⊆ ker N_G`, also only a target here). The definition itself has no
generation hypothesis.

**`herbrandH0CommGroup`**, **`herbrandHMinusOneCommGroup`** (M113.030,
M113.031). Telescope: finite core (and `(σ : G)` for M113.031). Types
`CommGroup (HerbrandH0 G A)` and `CommGroup (HerbrandHMinusOne G A σ)`. Each
body is the source tactic block `unfold …; infer_instance`, which yields
Mathlib's quotient-group structure on the quotient of a commutative group.

**`HerbrandH0.equiv`**, **`HerbrandHMinusOne.equiv`** (M113.032, M113.033).
Telescope: finite core (and `(σ : G)`). Types
`HerbrandH0 G A ≃* fixedSubgroup G A ⧸ (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)`
and the analogous `HerbrandHMinusOne G A σ ≃* normKernelSubgroup G A ⧸ …`.
Each body is the source block `change …; exact MulEquiv.refl _`: the identity,
since the Herbrand group is by definition that quotient.

**`HerbrandH0.mk`**, **`HerbrandHMinusOne.mk`** (M113.034, M113.035).
Telescope: finite core (and `(σ : G)`). Types
`fixedSubgroup G A →* HerbrandH0 G A` and
`normKernelSubgroup G A →* HerbrandHMinusOne G A σ`. Each body is the source
block `unfold …; exact QuotientGroup.mk' …`, the quotient map.

**`herbrandH0FiniteOfFinite`**, **`herbrandHMinusOneFiniteOfFinite`**
(M113.056, M113.057). Telescope: finite core, then `(σ : G)` for M113.057,
then `[Finite A]`. Types `Finite (HerbrandH0 G A)` and
`Finite (HerbrandHMinusOne G A σ)`. Each body is
`Finite.of_equiv` applied to the raw quotient and `(… .equiv …).symm.toEquiv`,
as in the source. Both are `noncomputable instance`, as in the source.

**`rightRegularFunctionTateNormSubgroup`** (M113.059, `abbrev`). Telescope:
finite rr. Type `Subgroup (G → B)`. Body:
`letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)` followed
by `exact tateNormSubgroup G (G → B)`, the norm group of the right-regular
module `G → B`.

**`rightRegularFunctionHerbrandH0`** (M113.060, `def`). Telescope: finite rr.
The source gives no result type. Its type is inferred, as in the source, to
be `Type (max uG uB)`. Body: the same `letI`, then
`exact HerbrandH0 G (G → B)`.

**`rightRegularFunctionHerbrandH0CommGroup`** (M113.061,
`noncomputable instance`). Telescope: finite rr. Type
`CommGroup (rightRegularFunctionHerbrandH0 (G := G) (B := B))`. Body: the
`letI`, `change CommGroup (HerbrandH0 G (G → B))`, `infer_instance`.

**`rightRegularFunctionNormKernelSubgroup`** (M113.062, `abbrev`). Telescope:
finite rr. Type `Subgroup (G → B)`. Body: the `letI`, then
`exact normKernelSubgroup G (G → B)`.

**`rightRegularFunctionAugmentationSubgroup`** (M113.063, `abbrev`).
Telescope: `{G : Type uG} {B : Type uB} [Group G] [CommGroup B]` (its `omit`
also removes `[Fintype G]`), then `(σ : G)`. Type `Subgroup (G → B)`. Body:
the `letI`, then `exact augmentationSubgroup G (G → B) σ`.

**`rightRegularFunctionHerbrandHMinusOne`** (M113.064, `def`). Telescope:
finite rr, then `(σ : G)`. No result type in the source. The inferred type is
`Type (max uG uB)`. Body: the `letI`, then
`exact HerbrandHMinusOne G (G → B) σ`.

**`rightRegularFunctionHerbrandHMinusOneCommGroup`** (M113.065,
`noncomputable instance`). Telescope: finite rr, then `(σ : G)`. Type
`CommGroup (rightRegularFunctionHerbrandHMinusOne (G := G) (B := B) σ)`.
Body: the `letI`, `change CommGroup (HerbrandHMinusOne G (G → B) σ)`,
`infer_instance`.

**Instances.** The six instances M113.030, M113.031, M113.056, M113.057,
M113.061 and M113.065 are global, exactly as in the source, which has no
`local` or `scoped` modifier on them. Each has the default priority. Their
classes are applied to the new semireducible `def`s `HerbrandH0`,
`HerbrandHMinusOne`, `rightRegularFunctionHerbrandH0` and
`rightRegularFunctionHerbrandHMinusOne`, which no Mathlib or other Library
declaration mentions. So they cannot overlap with an existing instance. A
search of the Library at commit `457e31a2131a1083c26931d33fec09a71fea54d6`
found no declaration with any of the twenty-two names. None of the extracted
source declarations is `private` or anonymous.

## Original-to-adapted map and modifications (Worker 9)

- **Extraction**: only the twenty-two declarations in the table (source lines
  183–189, 219–225, 251–264, 315–386, 681–699 and 709–768), with the section
  context of lines 24–33 and 62–64, are taken. The theorems of this task, for
  example `tateNormHom_apply` at lines 191–196, are Prop-valued targets in
  `Statements.lean` and `RightRegularStatements.lean` beside this file.
  M113.058 `rightRegularFunctionFixedSubgroup` (lines 701–707) is already in
  the Library module `Basic.RightRegularDefinitions`.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  The nested `ProfiniteCohomology.Herbrand` namespaces, `noncomputable section`,
  `open scoped BigOperators` and the `universe uG uA uB uC` declaration are
  kept.
- **Imports**: the source's nine Mathlib imports (lines 7–15) are replaced by
  the three published proof modules
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U011.Proofs`
  (`tateNorm_mul`, M113.011),
  `….Basic.U012.Proofs` (`tateNorm_one`, M113.012) and
  `….Basic.U017.Proofs` (`sigmaMinusOne_mul`, M113.017). Each imports the
  published `Basic.Statements`, which imports `Basic.Definitions`, which
  carries the nine Mathlib imports unchanged. The source file has no NYLL
  imports.
- **Proof fields citing source theorems**: the `map_one'` and `map_mul'`
  fields of M113.013 and the `map_mul'` field of M113.018 cite
  `tateNorm_one`, `tateNorm_mul` and `sigmaMinusOne_mul` by name with the same
  named arguments as the source. In the source these are theorems of the same
  file. Here they are the published theorems whose types are the closed
  Prop-valued targets `tateNorm_oneStatement`, `tateNorm_mulStatement` and
  `sigmaMinusOne_mulStatement` of `Basic.Statements`. The elaborated field
  terms are the same applications of these constants, as the audit below
  confirms.
- **Section variables**: the source declares
  `{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`,
  `[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and
  `[MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]`
  at lines 62–64. For each declaration that uses them, the adapted file
  writes the variables remaining after its `omit … in` and used by the
  declaration as explicit binders of that declaration, in the order of lines
  62–64 and with the same binder kinds, and uses no `variable` or `omit`
  command. M113.021–M113.023, M113.028 and M113.029 declare their own binders
  in the source and are copied unchanged.
- **Declarations**: names, universes, binders, binder kinds, types, bodies,
  every proof field and every tactic block are otherwise unchanged. The
  `abbrev` of M113.059, M113.062 and M113.063 and the `noncomputable`
  modifier of M113.056, M113.057, M113.061 and M113.065 are kept. M113.060
  and M113.064 keep the source's missing result-type ascription.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings against the three published
  proof modules.
- A private audit module compiles an unmodified copy of the complete pinned
  source file (SHA-256 above; it has no NYLL imports and no `sorry`) beside
  this module and its two sibling statement modules. Starting from the
  twenty-two units here and the thirty-four source theorems of the sibling
  targets, it follows every `CyclicCohomology.*` constant used in a type, or
  in the value of a definition. This reaches 46 source constants: the
  twenty-two units, the Library constructions M113.001–M113.003, M113.009,
  M113.058 and M113.101, the theorems `tateNorm_one`, `tateNorm_mul` and
  `sigmaMinusOne_mul`, and the auxiliary `_proof_N` lemmas of the definitions.
  For each of them it checks in Lean's `MetaM` that:
  - the universe-parameter lists are identical;
  - types, and for definitions and `_proof_N` lemmas also values, are
    structurally equal (`Expr.equal`, which compares binder kinds). Before
    comparing, it renames original `CyclicCohomology.*` constants to
    `Langlands.NYLL.CyclicCohomology.*` and erases hygienic macro scopes from
    binder names (they encode the module name of anonymous instance
    binders). For the three cited theorems it compares the source theorem
    type with the unfolded value of the published `…Statement` target;
  - for definitions, instance status, instance priority, reducibility status,
    noncomputability, `protected` status, definition safety and reducibility
    hints agree.

  It also checks that the docstrings of the twenty-two units agree. Every
  check passed.
- A separate check in the audit module confirms that M113.060 and M113.064
  have type `Type (max uG uB)`.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The verbatim copy compiles unchanged at the project's pin, so no
  compatibility change was needed.

The private source copy and audit module are not part of this contribution.

## Scope

This unit supplies two homomorphisms, three subgroups, the two low-degree
Herbrand quotient groups with their group structures, identity equivalences,
quotient maps and finiteness instances, and their specializations to the
right-regular module `G → B`. Apart from the proof fields inherited from the
source, it proves nothing about them. In particular, the inclusions
`N_G A ⊆ A^G` and `(σ - 1)A ⊆ ker N_G`, the vanishing criteria and the
equality `#Ĥ⁰ = #Ĥ⁻¹` for finite cyclic modules are only targets in the
sibling statement modules. This unit asserts no Herbrand-quotient
multiplicativity, class-formation, cup-product, Tate, transfer or reciprocity
result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"). No other draft was reused. The three proof
modules imported here are separate publications of Task 6258. The retained
license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
