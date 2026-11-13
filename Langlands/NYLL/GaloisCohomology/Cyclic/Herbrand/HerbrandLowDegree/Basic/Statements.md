# NYLL M113 targets: `σ - 1` fixed points, finite cardinalities and Tate-norm algebra

This module extracts thirteen theorem types from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
closed Prop-valued definitions. It supplies targets only and contains no
proofs of them. Proofs are separate `lean.proof@1` work.

## Source

The original is
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` (1717
lines, SHA-256
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M113. The whole source file was read, including its section context (lines
24–33), its only `variable` commands (lines 62–64) and every `omit … in`
preceding the extracted theorems. The file contains no other `variable`,
`section`, `include` or `open` command before line 1713.

## Exact source and parameter map

All original names are in `CyclicCohomology.ProfiniteCohomology.Herbrand`; all
target names are in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
Append `Statement` to the original name to obtain the target's exact name.

The source section variables (lines 62–64) are
`{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`,
`[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and
`[MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]`.
Each theorem includes those that remain after its `omit … in` and that are
mentioned in its statement. They come first, in the order of lines 62–64. In
the table, write

- *core* for `{G : Type uG} {A : Type uA} [Group G] [CommGroup A] [MulDistribMulAction G A]`;
- *finite core* for `{G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]`;
- *pair* for `{G : Type uG} {A : Type uA} {B : Type uB} [Group G] [CommGroup A] [CommGroup B] [MulDistribMulAction G A] [MulDistribMulAction G B]`;
- *finite pair* for *pair* with `[Fintype G]` inserted after `[Group G]`.

These abbreviations describe the table only. The Lean definitions spell out
every binder.

| Unit | Original name; `omit` / docstring / asserted type lines | Paired Lean line | Complete telescope | Conclusion |
| --- | --- | --- | --- | --- |
| M113.004 | `smul_eq_of_mem_zpowers_of_sigmaMinusOne_eq_one`; 66–67 / 68–69 / 70–73 | 40 | core; `{σ g : G}`; `{a : A}`; `(hg : g ∈ Subgroup.zpowers σ)`; `(hσ : sigmaMinusOne G A σ a = 1)` | `g • a = a` |
| M113.005 | `fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one`; 78–79 / 80–81 / 82–85 | 50 | core; `{σ : G}`; `{a : A}`; `(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)`; `(hσ : sigmaMinusOne G A σ a = 1)` | `∀ g : G, g • a = a` |
| M113.006 | `monoidHom_card_eq_card_ker_mul_card_range`; 90–92 / 93–95 / 96–98 | 60 | no section variable; `{X : Type uA} {Y : Type uB} [Group X] [Group Y] [Finite X] (f : X →* Y)` | `Nat.card X = Nat.card (MonoidHom.ker f) * Nat.card (MonoidHom.range f)` |
| M113.007 | `monoidHom_card_eq_card_range_mul_card_range_of_exact`; 102–104 / 105–107 / 108–113 | 68 | no section variable; `{X : Type uA} {Y : Type uB} {Z : Type uC} [Group X] [Group Y] [Group Z] [Finite Y] (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)` | `Nat.card Y = Nat.card (MonoidHom.range f) * Nat.card (MonoidHom.range g)` |
| M113.008 | `card_subgroupOf_eq_card`; 116–118 / 119–120 / 121–123 | 78 | no section variable; `{X : Type uA} [Group X] [Finite X] {H K : Subgroup X} (hHK : H ≤ K)` | `Nat.card (H.subgroupOf K) = Nat.card H` |
| M113.010 | `map_tateNorm`; none / 154 / 155–157 | 84 | finite pair; `(f : A →* B)`; `(hf : ∀ (g : G) (a : A), f (g • a) = g • f a)`; `(a : A)` | `f (tateNorm G A a) = tateNorm G B (f a)` |
| M113.011 | `tateNorm_mul`; 161–162 / 163 / 164–165 | 93 | finite core; `(a b : A)` | `tateNorm G A (a * b) = tateNorm G A a * tateNorm G A b` |
| M113.012 | `tateNorm_one`; 175–176 / 177 (`@[simp]` 178) / 179 | 99 | finite core | `tateNorm G A 1 = 1` |
| M113.015 | `tateNorm_inv`; 199–200 / 201 / 202 | 105 | finite core; `(a : A)` | `tateNorm G A a⁻¹ = (tateNorm G A a)⁻¹` |
| M113.016 | `map_sigmaMinusOne`; 205 / 206 / 207–209 | 112 | pair; `(f : A →* B)`; `(hf : ∀ (g : G) (a : A), f (g • a) = g • f a)`; `(σ : G)`; `(a : A)` | `f (sigmaMinusOne G A σ a) = sigmaMinusOne G B σ (f a)` |
| M113.017 | `sigmaMinusOne_mul`; 212–213 / 214 / 215–216 | 121 | core; `(σ : G)`; `(a b : A)` | `sigmaMinusOne G A σ (a * b) = sigmaMinusOne G A σ a * sigmaMinusOne G A σ b` |
| M113.066 | `tateNorm_sigmaMinusOne_eq_one`; none / 770–771 / 772–773 | 128 | finite core; `(σ : G)`; `(a : A)` | `tateNorm G A (sigmaMinusOne G A σ a) = 1` |
| M113.068 | `smul_tateNorm_eq`; none / 799–800 / 801–802 | 135 | finite core; `(h : G)`; `(a : A)` | `h • tateNorm G A a = tateNorm G A a` |

M113.010, M113.066 and M113.068 have no `omit`. `C` and its instances are
not mentioned in their statements, so they are not included. M113.016 omits
`[Fintype G]`, so it holds for an arbitrary group. M113.006–M113.008 omit every
section variable and reuse the universe names `uA`, `uB` and `uC` for their own
groups `X`, `Y` and `Z`. These universes stay independent.

The definitions close the entire elaborated source telescope inside `∀`, so
each declaration type is `Prop`. Braces, parentheses and instance brackets
keep their source binder kinds. The proof premises `hg`, `hσ`, `hgen`,
`hexact`, `hHK` and `hf` remain named explicit binders with their source types.
The unused-variable linter is disabled locally, with
`set_option linter.unusedVariables false in`, only for the six definitions
whose named premises do not occur in their conclusions: M113.004, M113.005,
M113.007, M113.008, M113.010 and M113.016.

`tateNorm`, `sigmaMinusOne` and the `G`-actions are the actual constructions of
the sibling `Definitions` module (M113.001 and M113.002). `MonoidHom.ker`,
`MonoidHom.range`, `Subgroup.subgroupOf`, `Subgroup.zpowers` and `Nat.card` are
Mathlib's.

## Modifications (Worker 5086)

- **Extraction**: only the asserted types are taken. Every proof body (for
  example source lines 74–76 and 166–173) is omitted, and so is the `@[simp]`
  attribute of `tateNorm_one` (line 178), which has no meaning on a
  Prop-valued definition. The source proof of `tateNorm_inv` uses M113.013
  `tateNormHom`, which task revision 2 excludes. The statement does not need
  it. M113.013, M113.014 `tateNormHom_apply`, M113.018 `sigmaMinusOneHom` and
  the Herbrand-group units are not part of this module.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
- **Section variables**: written as explicit `∀` binders in the order of lines
  62–64, followed by each theorem's own binders. No `variable` or `omit`
  command is used.
- **Imports**: the sole import is the sibling module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`,
  which carries the source's nine Mathlib imports. Nothing is redefined here.
- **Docstrings**: the declaration docstrings are the source theorem
  docstrings. The module docstring is a modification notice. A comment records
  why the linter is disabled.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection reports that
  `tateNorm_mulStatement` has type `Prop`.
- A private audit module compiles an unmodified copy of the complete pinned
  source file beside this module. For each of the thirteen theorems it checks
  in `MetaM` that the theorem and its target have identical universe-parameter
  lists, that the target's type is `Prop`, and that the target's value is
  structurally equal (`Expr.equal`, which compares binder kinds) to the
  original theorem type. Before comparing, it renames original
  `CyclicCohomology.*` constants to `Langlands.NYLL.CyclicCohomology.*` and
  erases hygienic macro scopes from binder names. It also checks with
  `isDefEq` that each unapplied target constant is definitionally equal to the
  type of the original theorem constant at the same universe parameters. All
  thirteen checks passed.

The private source copy and audit module are not part of this contribution.
They establish the correspondence during development and publish no proofs.

## Scope

These targets assert elementary facts about the Tate norm, the coboundary
`σ - 1`, fixed points under a cyclic generator and finite group cardinalities.
They do not assert a class-formation, cup-product, Tate, transfer or
reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
