# NYLL M113.001–M113.003 and M113.009: Tate norm, `σ - 1`, fixed subgroup and the right-regular action

## Source

The paired Lean file extracts four declarations from Naganori Yamaguchi's
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
M113 (patch status "none in patch10").

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M113.001 | `CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm`, `def` at line 37 (lines 35–39) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm` (line 44) |
| M113.002 | `CyclicCohomology.ProfiniteCohomology.Herbrand.sigmaMinusOne`, `def` at line 42 (lines 41–44) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.sigmaMinusOne` (line 49) |
| M113.003 | `CyclicCohomology.ProfiniteCohomology.Herbrand.fixedSubgroup`, `def` at line 47 (lines 46–60) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.fixedSubgroup` (line 54) |
| M113.009 | `CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularFunctionMulDistribMulAction`, `@[reducible] def` at line 132 (`omit` lines 126–128, docstring 129–131, end 152) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularFunctionMulDistribMulAction` (line 72) |

The section context is source lines 24–33: `namespace CyclicCohomology`,
`noncomputable section`, `open scoped BigOperators`,
`namespace ProfiniteCohomology`, `namespace Herbrand` and
`universe uG uA uB uC`. The adapted file reproduces it inside
`namespace Langlands.NYLL.CyclicCohomology` and closes it as at source lines
1713–1717.

## The declarations

**`tateNorm`** (M113.001). Telescope: explicit `G : Type uG` and
`A : Type uA` at independent universes, instance-implicit `[Group G]`,
`[Fintype G]`, `[CommGroup A]` and `[MulDistribMulAction G A]`, and an explicit
`a : A`. The value is the finite product `∏ g : G, g • a` over
`Finset.univ`, that is the norm `N_G a` of a multiplicative `G`-module.

**`sigmaMinusOne`** (M113.002). Telescope: explicit `G : Type uG`,
`A : Type uA`, `[Group G]`, `[CommGroup A]`, `[MulDistribMulAction G A]`,
explicit `σ : G` and `a : A`. No finiteness of `G` is assumed. The value is
`σ • a * a⁻¹`, the multiplicative coboundary `a^(σ-1)`.

**`fixedSubgroup`** (M113.003). Telescope: explicit `G : Type uG`,
`A : Type uA`, `[Group G]`, `[CommGroup A]`, `[MulDistribMulAction G A]`. The
value is the subgroup of `A` with carrier `{a | ∀ g : G, g • a = a}`, that is
`A^G`. Its `one_mem'`, `mul_mem'` and `inv_mem'` fields are the source's
tactic proofs, using `MulDistribMulAction.smul_one`,
`MulDistribMulAction.smul_mul` and `smul_inv'`. A private check confirms by
`rfl` that `fixedSubgroup G A = FixedPoints.subgroup G A` for Mathlib's
fixed-point subgroup (`Mathlib/GroupTheory/GroupAction/Defs.lean`). The
source's own construction is kept, as the task requires.

**`rightRegularFunctionMulDistribMulAction`** (M113.009). Telescope: implicit
`{G : Type uG}` and `{B : Type uB}`, then `[Group G]` and `[CommGroup B]`. The
result type is `MulDistribMulAction G (G → B)`, where `G → B` carries
Mathlib's pointwise `CommGroup` structure. The action is
`g • f = fun x => f (x * g)`, the right-regular action on functions: the
multiplicative module induced from the trivial subgroup. The `one_smul`,
`mul_smul`, `smul_mul` and `smul_one` fields are the source's tactic proofs. A
private check confirms by `rfl` that `(g • f) x = f (x * g)` under this action.
The declaration is a `@[reducible] def`, not an `instance`, exactly as in the
source. It adds no global instance. Uses install it locally with `letI`, as
the source does. Mathlib's `arrowAction` (`Mathlib/Algebra/Group/Action/Basic.lean`)
is a different action, `(g • F) a = F (g⁻¹ • a)`, and only a `MulAction`.

## Original-to-adapted map and modifications (Worker 5086)

- **Extraction**: only source lines 35–60 and 126–152, with the section
  context of lines 24–33 and 62–64, are taken. The other listed M113 units are
  in `Statements.lean` beside this file and in the right-regular modules of
  this directory. M113.013 `tateNormHom` and M113.018 `sigmaMinusOneHom` are not
  ported here: task revision 2 routes them later with the proofs of M113.011,
  M113.012 and M113.017, which are their `map_one'` and `map_mul'` fields.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  The nested `ProfiniteCohomology.Herbrand` namespaces, `noncomputable section`,
  `open scoped BigOperators` and the `universe uG uA uB uC` declaration are
  kept.
- **Imports**: the source's nine Mathlib imports (lines 7–15) are kept
  unchanged and in order. The source module has no NYLL imports.
- **Section variables**: the source declares
  `{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`,
  `[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and
  `[MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]`
  at lines 62–64. M113.009 removes `[Fintype G] [CommGroup A] [CommGroup C]`
  and the three action instances with `omit … in` (lines 126–128). The adapted
  file writes the remaining variables `{G : Type uG} {B : Type uB} [Group G]
  [CommGroup B]` as explicit binders of the definition, in the same order and
  with the same binder kinds, and uses no `variable` or `omit` command.
  M113.001–M113.003 precede the `variable` lines and are copied unchanged.
- **Declarations**: names, universes, binders, binder kinds, types, bodies
  and every proof field are otherwise unchanged. The `@[reducible]` attribute
  of M113.009 is kept. None of the four is marked `noncomputable` in the
  source, and none is compiled as noncomputable here.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module compiles an unmodified copy of the complete pinned
  source file (SHA-256 above; no NYLL imports are needed) beside this file.
  For each of the four declarations it checks, in Lean's `MetaM`, that the
  universe-parameter lists are identical and that the original and adapted
  declaration types and values are structurally equal (`Expr.equal`, which
  compares binder kinds). Before comparing, it renames original
  `CyclicCohomology.*` constants to `Langlands.NYLL.CyclicCohomology.*` and
  erases hygienic macro scopes from binder names. Those scopes encode the
  module name of anonymous instance binders. The audit also checks that
  reducibility status and noncomputability agree. All four checks passed.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The verbatim copy compiles unchanged at the project's pin, so no
  compatibility change was needed.

## Scope

This unit supplies three constructions and one action structure. It proves
nothing about them and asserts no host class-formation, cup-product, Tate,
transfer or reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
