# NYLL M113.058, M113.080, M113.085, M113.089, M113.101 and M113.103: right-regular cyclic primitives and transport data

## Source

The paired Lean file extracts six declarations from Naganori Yamaguchi's
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

All original names are in `CyclicCohomology.ProfiniteCohomology.Herbrand`.
Each adapted name is the original name with the prefix `Langlands.NYLL`, in
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.

| Unit | Source declaration; `omit` / docstring / declaration line / end | Kind | Paired Lean line |
| --- | --- | --- | --- |
| M113.058 | `rightRegularFunctionFixedSubgroup`; 701–703 / 704 / 705 / 707 | `abbrev` | 38 |
| M113.080 | `rightRegularCyclicPartialProduct`; 1029–1031 / 1032–1034 / 1035 / 1036 | `def` | 46 |
| M113.085 | `rightRegularCyclicIndex`; 1090–1092 / 1093–1094 / 1095 / 1098 | `noncomputable def` | 53 |
| M113.089 | `rightRegularCyclicPrimitive`; 1137–1139 / 1140–1141 / 1142 / 1146 | `noncomputable def` | 61 |
| M113.101 | `multiplicativeMulDistribMulActionOfDistribMulAction`; 1466–1468 / 1469–1470 / 1471 / 1497 | `@[reducible] def` | 70 |
| M113.103 | `mulEquivRightRegularFunctionOfAddEquiv`; 1521–1523 / 1524–1525 / 1526 / 1557 | `def` | 100 |

The section context is source lines 24–33: `namespace CyclicCohomology`,
`noncomputable section`, `open scoped BigOperators`,
`namespace ProfiniteCohomology`, `namespace Herbrand` and
`universe uG uA uB uC`. The adapted file reproduces it inside
`namespace Langlands.NYLL.CyclicCohomology` and closes it as at source lines
1713–1717.

## The declarations

The source section variables (lines 62–64) are
`{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`,
`[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and
`[MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]`.
A declaration includes the variables that remain after its `omit … in` and
that it mentions. They come first, in the order of lines 62–64, and the
declaration's own binders follow.

**`rightRegularFunctionFixedSubgroup`** (M113.058). Telescope:
`{G : Type uG} {B : Type uB} [Group G] [CommGroup B]`. The `omit` (lines
701–703) removes `[Fintype G]`, `[CommGroup A]`, `[CommGroup C]` and all three
`MulDistribMulAction` instances. The result type is
`Subgroup (G → B)`. The body is the source tactic block: it installs the
right-regular action `rightRegularFunctionMulDistribMulAction` (M113.009,
`(g • f) x = f (x * g)`) locally with `letI` and returns
`fixedSubgroup G (G → B)` (M113.003). So the value is the subgroup of
functions `f : G → B` with `f (x * g) = f x` for all `g` and `x`, the
`G`-invariants of the multiplicative module induced from the trivial
subgroup. This file proves nothing about it, in particular not that these are
the constant functions.

**`rightRegularCyclicPartialProduct`** (M113.080). Telescope:
`{G : Type uG} {B : Type uB} [Group G] [CommGroup B]`, then explicit
`(σ : G) (f : G → B) (i : ℕ)`. The value is
`(Finset.range i).prod (fun k => f (σ ^ k))`, that is
`f (σ ^ 0) * f (σ ^ 1) * ⋯ * f (σ ^ (i - 1))`, with value `1` at `i = 0`.

**`rightRegularCyclicIndex`** (M113.085). Telescope:
`{G : Type uG} [Group G] [Fintype G]`, then explicit `(σ : G)`,
`(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)` and `(x : G)`. The result type is
`ZMod (Fintype.card G)`. The value is
`Classical.choose (IsCyclic.unique_zpow_zmod (a := σ) hgen x)`. Mathlib's
`IsCyclic.unique_zpow_zmod`
(`Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean`) states, for a
generator `σ` of a finite group, `∃! n : ZMod (Fintype.card G), x = σ ^ n.val`.
The definition selects that index with the axiom of choice, so it is
noncomputable, as in the source.

**`rightRegularCyclicPrimitive`** (M113.089). Telescope:
`{G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]`, then
explicit `(σ : G)`, `(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)` and
`(f : G → B)`. The result is the function `G → B` sending `x` to
`rightRegularCyclicPartialProduct σ f (rightRegularCyclicIndex σ hgen x).val`.
In words: if `x = σ ^ i` with `0 ≤ i < |G|`, the value at `x` is
`f (σ ^ 0) * ⋯ * f (σ ^ (i - 1))`. The source uses it to solve
`b (x * σ) * (b x)⁻¹ = f x` on the right-regular module. That property is the
target M113.092 in `RightRegularStatements.lean` beside this file and is not
proved here.

**`multiplicativeMulDistribMulActionOfDistribMulAction`** (M113.101). Telescope:
explicit `(G : Type uG) (M : Type uA)`, then `[Group G]`, `[AddCommGroup M]` and
`[DistribMulAction G M]`. These are the declaration's own binders. The source
`omit` (lines 1466–1468) removes the `CommGroup` and `MulDistribMulAction`
section instances but keeps `[Group G]` and `[Fintype G]`. The explicit binder
`G` shadows the section variable `G`, so no section variable is included (the private audit confirms this telescope against the
compiled source). The result type is `MulDistribMulAction G (Multiplicative M)`
with `g • m = Multiplicative.ofAdd (g • Multiplicative.toAdd m)`: the action on
an additive `G`-module, transported to its multiplicative wrapper. The
`one_smul`, `mul_smul`, `smul_mul` and `smul_one` fields are the source tactic
proofs. The declaration is a `@[reducible] def`, not an `instance`, exactly as
in the source; it adds no global instance. Uses install it locally with
`letI`, as M113.104 does.

**`mulEquivRightRegularFunctionOfAddEquiv`** (M113.103). Telescope: explicit
`(G : Type uG)`, implicit `{M : Type uA} {D : Type uB}`, then
`[AddCommGroup M] [AddCommGroup D]` and explicit `(e : M ≃+ (G → D))`. The
source `omit` (lines 1521–1523) removes every section instance, including
`[Group G]`, and no section variable is included; the explicit binder `G` is a
bare type. The result type is
`Multiplicative M ≃* (G → Multiplicative D)`: `toFun m` is
`fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd m) x)` and `invFun f`
is `Multiplicative.ofAdd (e.symm (fun x => Multiplicative.toAdd (f x)))`. The
`left_inv`, `right_inv` and `map_mul'` fields are the source tactic proofs.
It turns an additive identification of `M` with functions `G → D` into a
multiplicative identification with functions `G → Multiplicative D`.

## Original-to-adapted map and modifications (Worker 5086)

- **Extraction**: only the six declarations in the table are taken, each with
  its docstring. Source lines between them (other definitions, theorems and
  proofs) are not part of this file. The sibling `Definitions.lean` holds
  M113.001–M113.003 and M113.009. `Statements.lean` and
  `RightRegularStatements.lean` hold the listed theorem targets. M113.081
  `rightRegularCyclicPartialProduct_zero` and M113.102
  `multiplicativeFunctionMulEquiv` are not in the task list, and no listed
  declaration needs them.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  The nested `ProfiniteCohomology.Herbrand` namespaces, `noncomputable section`,
  `open scoped BigOperators` and the `universe uG uA uB uC` declaration are
  kept.
- **Imports**: the sole import is the sibling module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`.
  It carries the source's nine Mathlib imports (lines 7–15) and the adapted
  `fixedSubgroup` and `rightRegularFunctionMulDistribMulAction` that M113.058
  uses. Nothing is redefined here.
- **Section variables**: M113.058, M113.080, M113.085 and M113.089 include
  section variables. The adapted file writes each included variable as an
  explicit binder of the definition, in the order of lines 62–64 and with the
  same binder kind, followed by the declaration's own binders. M113.101 and
  M113.103 include none and are unchanged. No `variable` or `omit` command is
  used.
- **Declarations**: names (apart from the prefix), universes, binders, binder
  kinds, types, bodies and every proof field are otherwise unchanged. The
  `abbrev` of M113.058, the `@[reducible]` attribute of M113.101 and the
  `noncomputable` markers of M113.085 and M113.089 are kept.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module compiles an unmodified copy of the complete pinned
  source file (SHA-256 above; no NYLL imports are needed) beside this file.
  For each of the six declarations it checks, in Lean's `MetaM`, that the
  universe-parameter lists are identical and that the original and adapted
  declaration types and values are structurally equal (`Expr.equal`, which
  compares binder kinds). Before comparing, it renames original
  `CyclicCohomology.*` constants to `Langlands.NYLL.CyclicCohomology.*` and
  erases hygienic macro scopes from binder names. Those scopes encode the
  module name of anonymous instance binders. The audit also checks that
  reducibility status and noncomputability agree. All six checks passed.
  The universe parameters are `uG uB` for M113.058, M113.080 and M113.089,
  `uG` for M113.085, `uG uA` for M113.101 and `uG uA uB` for M113.103.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The verbatim copy compiles unchanged at the project's pin, so no
  compatibility change was needed.

## Scope

This unit supplies a subgroup, two cyclic product constructions, a chosen
index, an action structure and a multiplicative equivalence. It proves
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
