# NYLL M113 targets: evaluation of the norm and `σ - 1` homomorphisms, cardinality factorizations, Herbrand quotient maps and vanishing criteria

This module extracts twenty-five theorem types from Naganori Yamaguchi's
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
Append `Statement` to the original name to obtain the target's exact name
(for example `HerbrandH0.equiv_mk` becomes `HerbrandH0.equiv_mkStatement`).

The source section variables (lines 62–64) are
`{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`,
`[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and
`[MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]`.
Each theorem includes the variables that remain after its `omit … in` and
that its statement mentions, together with the remaining instance variables
whose types mention only included variables. They come first, in the order of
lines 62–64. In the table, write

- *core* for `{G : Type uG} {A : Type uA} [Group G] [CommGroup A] [MulDistribMulAction G A]`
  (the `omit` removes `[Fintype G]`, `[CommGroup B]`, `[CommGroup C]` and the
  actions on `B` and `C`);
- *finite core* for `{G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]`;
- *finite pair* for `{G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G] [CommGroup A] [CommGroup B] [MulDistribMulAction G A] [MulDistribMulAction G B]`
  (the `omit` removes `[CommGroup C]` and the action on `C`);
- *hgen* for `(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)`, and *he* for
  `(he : ∀ (g : G) (a : A), e (g • a) = g • e a)`.

These abbreviations describe the table only. The Lean definitions spell out
every binder and every term.

| Unit | Original name; `omit` / docstring / asserted type lines | Paired Lean line | Complete telescope | Conclusion |
| --- | --- | --- | --- | --- |
| M113.014 | `tateNormHom_apply`; 191–192 / 193 (`@[simp]` 194) / 195–196 | 39 | finite core; `(a : A)` | `tateNormHom (G := G) (A := A) a = tateNorm G A a` |
| M113.019 | `sigmaMinusOneHom_apply`; 227–228 / 229 (`@[simp]` 230) / 231–232 | 45 | core; `(σ : G) (a : A)` | `sigmaMinusOneHom (G := G) (A := A) σ a = sigmaMinusOne G A σ a` |
| M113.024 | `sigmaMinusOneHom_ker_eq_fixedSubgroup`; 266–267 / 268 / 269–271 | 53 | core; `(σ : G)` hgen | `MonoidHom.ker (sigmaMinusOneHom (G := G) (A := A) σ) = fixedSubgroup G A` |
| M113.025 | `card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup`; 281–282 / 283–284 / 285–286 | 61 | finite core; `[Finite A]` | `Nat.card A = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A)` |
| M113.026 | `card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup`; 290–291 / 292–294 / 295–297 | 70 | core; `(σ : G)` hgen `[Finite A]` | `Nat.card A = Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ)` |
| M113.027 | `herbrand_finite_module_cardinality_balance`; 303–304 / 305–306 / 307–310 | 79 | finite core; `(σ : G)` hgen `[Finite A]` | `Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A)` |
| M113.036 | `HerbrandH0.equiv_mk`; 388–389 / 390 (`@[simp]` 391) / 392–394 | 87 | finite core; `(a : fixedSubgroup G A)` | `HerbrandH0.equiv (G := G) (A := A) (HerbrandH0.mk a) = QuotientGroup.mk a` |
| M113.037 | `HerbrandHMinusOne.equiv_mk`; 397–398 / 399–400 (`@[simp]` 401) / 402–405 | 95 | finite core; `(σ : G) (a : normKernelSubgroup G A)` | `HerbrandHMinusOne.equiv (G := G) (A := A) σ (HerbrandHMinusOne.mk σ a) = QuotientGroup.mk a` |
| M113.038 | `HerbrandH0.mk_surjective`; 408–409 / 410 / 411–412 | 103 | finite core | `Function.Surjective (HerbrandH0.mk (G := G) (A := A))` |
| M113.039 | `HerbrandHMinusOne.mk_surjective`; 421–422 / 423 / 424–425 | 109 | finite core; `(σ : G)` | `Function.Surjective (HerbrandHMinusOne.mk (G := G) (A := A) σ)` |
| M113.040 | `HerbrandH0.mk_eq_one_iff`; 434–435 / 436–437 (`@[simp]` 438) / 439–440 | 116 | finite core; `(a : fixedSubgroup G A)` | `HerbrandH0.mk a = 1 ↔ (a : A) ∈ tateNormSubgroup G A` |
| M113.041 | `HerbrandHMinusOne.mk_eq_one_iff`; 457–458 / 459–460 (`@[simp]` 461) / 462–465 | 123 | finite core; `(σ : G) (a : normKernelSubgroup G A)` | `HerbrandHMinusOne.mk σ a = 1 ↔ (a : A) ∈ augmentationSubgroup G A σ` |
| M113.046 | `HerbrandH0.inductionOn` (`protected`); 562–563 / 564–565 / 566–568 | 133 | finite core; `{motive : HerbrandH0 G A → Prop} (q : HerbrandH0 G A) (h : ∀ a : fixedSubgroup G A, motive (HerbrandH0.mk a))` | `motive q` |
| M113.047 | `HerbrandHMinusOne.inductionOn` (`protected`); 572–573 / 574–575 / 576–580 | 142 | finite core; `(σ : G) {motive : HerbrandHMinusOne G A σ → Prop} (q : HerbrandHMinusOne G A σ) (h : ∀ a : normKernelSubgroup G A, motive (HerbrandHMinusOne.mk σ a))` | `motive q` |
| M113.067 | `augmentationSubgroup_le_normKernelSubgroup`; none / 792 / 793–794 | 151 | finite core; `(σ : G)` | `augmentationSubgroup G A σ ≤ normKernelSubgroup G A` |
| M113.069 | `tateNormSubgroup_le_fixedSubgroup`; none / 818 / 819–820 | 157 | finite core | `tateNormSubgroup G A ≤ fixedSubgroup G A` |
| M113.070 | `herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup`; 825–826 / 827–828 / 829–831 | 165 | finite core; `(h : fixedSubgroup G A ≤ tateNormSubgroup G A)` | `Subsingleton (HerbrandH0 G A)` |
| M113.072 | `herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup`; 857–858 / 859–861 / 862–864 | 175 | finite core; `(σ : G) (h : normKernelSubgroup G A ≤ augmentationSubgroup G A σ)` | `Subsingleton (HerbrandHMinusOne G A σ)` |
| M113.075 | `fixed_le_tateNormSubgroup_of_mulEquiv`; 906 / 907–908 / 909–913 | 184 | finite pair; `(e : A ≃* B)` he `(hB : fixedSubgroup G B ≤ tateNormSubgroup G B)` | `fixedSubgroup G A ≤ tateNormSubgroup G A` |
| M113.076 | `normKernel_le_augmentationSubgroup_of_mulEquiv`; 929 / 930–931 / 932–936 | 196 | finite pair; `(e : A ≃* B)` he `(σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ)` | `normKernelSubgroup G A ≤ augmentationSubgroup G A σ` |
| M113.077 | `herbrandH0_subsingleton_of_mulEquiv`; 959 / 960–961 / 962–966 | 208 | finite pair; `(e : A ≃* B)` he `(hB : fixedSubgroup G B ≤ tateNormSubgroup G B)` | `Subsingleton (HerbrandH0 G A)` |
| M113.078 | `herbrandHMinusOne_subsingleton_of_mulEquiv`; 971 / 972–973 / 974–978 | 220 | finite pair; `(e : A ≃* B)` he `(σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ)` | `Subsingleton (HerbrandHMinusOne G A σ)` |
| M113.107 | `card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup`; 1650–1651 / 1652 / 1653–1655 | 230 | finite core; `[Finite A]` | `Nat.card (fixedSubgroup G A) = Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A)` |
| M113.108 | `card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup`; 1661–1662 / 1663–1664 / 1665–1669 | 238 | finite core; `(σ : G) [Finite A]` | `Nat.card (normKernelSubgroup G A) = Nat.card (HerbrandHMinusOne G A σ) * Nat.card (augmentationSubgroup G A σ)` |
| M113.109 | `herbrand_finite_module_card_eq`; 1675–1676 / 1677–1678 / 1679–1681 | 250 | finite core; `(σ : G)` hgen `[Finite A]` | `Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)` |

The `omit` of M113.019, M113.024 and M113.026 removes `[Fintype G]`,
`[CommGroup B]`, `[CommGroup C]` and the actions on `B` and `C` (core), so
these three targets concern an arbitrary group `G`. The `omit` of
M113.075–M113.078 removes only `[CommGroup C]` and the action on `C` (finite
pair). Every other `omit` in the table removes `[CommGroup B]`,
`[CommGroup C]` and the actions on `B` and `C` (finite core). M113.067 and
M113.069 have no `omit`. Their statements mention `G` and `A` but neither `B`
nor `C`, so the section variables they include are again the finite core.

The definitions close the entire elaborated source telescope inside `∀`, so
each declaration type is `Prop`. Braces, parentheses and instance brackets
keep their source binder kinds, and every hypothesis keeps its source name,
type and position. In M113.026 and M113.027 the instance `[Finite A]` comes
after `σ` and `hgen`, and in M113.108 after `σ`, as in the source. The
unused-variable linter is disabled locally, with
`set_option linter.unusedVariables false in` and a comment, only for the
twelve definitions whose named premises do not occur in their conclusions:
M113.024, M113.026, M113.027, M113.046, M113.047, M113.070, M113.072,
M113.075–M113.078 and M113.109.

## Meaning of the targets

`tateNormHom`, `sigmaMinusOneHom`, `tateNormSubgroup` (`N_G A`),
`normKernelSubgroup` (`ker N_G`), `augmentationSubgroup G A σ` (the image
`(σ - 1)A` of `a ↦ σ • a * a⁻¹`), `HerbrandH0` (`A^G` modulo `N_G A`),
`HerbrandHMinusOne` (`ker N_G` modulo `(σ - 1)A`) and their `equiv` and `mk`
maps are the constructions of the sibling module `Definitions.lean`.
`tateNorm`, `sigmaMinusOne` and `fixedSubgroup` (`A^G`) are the published
constructions of `Basic.Definitions`. `MonoidHom.ker`, `QuotientGroup.mk`,
`Subgroup.zpowers`, `Function.Surjective`, `Subsingleton` and `Nat.card` are
Mathlib's.

- M113.014 and M113.019 say that the two homomorphisms evaluate to `tateNorm`
  and `sigmaMinusOne`.
- M113.024: if `σ` generates `G`, the kernel of `a ↦ a^(σ-1)` is `A^G`.
- M113.025–M113.027: for finite `A`, `#A = #ker N_G · #N_G A`, and, when `σ`
  generates `G`, `#A = #A^G · #(σ - 1)A` and so
  `#A^G · #(σ - 1)A = #ker N_G · #N_G A`.
- M113.036–M113.041 and M113.046–M113.047: the identity equivalence sends the
  class map `mk` to Mathlib's quotient map, `mk` is surjective, its kernel is
  `N_G A` (in degree 0) or `(σ - 1)A` (in degree −1), and every class has a
  representative.
- M113.067 and M113.069: `(σ - 1)A ⊆ ker N_G` for every `σ`, and
  `N_G A ⊆ A^G`.
- M113.070 and M113.072: the quotients are subsingletons when
  `A^G ⊆ N_G A`, respectively `ker N_G ⊆ (σ - 1)A`.
- M113.075–M113.078: these inclusions, and hence the vanishing, transfer from
  `B` to `A` along a `G`-equivariant multiplicative equivalence `e : A ≃* B`.
- M113.107 and M113.108: for finite `A`,
  `#A^G = #HerbrandH0 G A · #N_G A` and
  `#ker N_G = #HerbrandHMinusOne G A σ · #(σ - 1)A`.
- M113.109: for finite `A` and a generator `σ` of `G`, the two Herbrand
  quotients have the same cardinality (Herbrand quotient `1`).

## Modifications (Worker 9)

- **Extraction**: only the asserted types are taken. Every proof body is
  omitted, and so are the `@[simp]` attributes of M113.014, M113.019,
  M113.036, M113.037, M113.040 and M113.041 (lines 194, 230, 391, 401, 438
  and 461), which have no meaning on a Prop-valued definition. The `protected`
  modifier of M113.046 and M113.047 is kept on the targets.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
- **Section variables**: written as explicit `∀` binders in the order of lines
  62–64, followed by each theorem's own binders. No `variable` or `omit`
  command is used.
- **Imports**: the sole import is the sibling module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`,
  which provides the constructions above and, through the published `Basic`
  modules, the source's nine Mathlib imports. Nothing is redefined here.
- **Docstrings**: the declaration docstrings are the source theorem
  docstrings. The module docstring is a modification notice. A comment records
  why the linter is disabled.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- The project's declaration inspection of the entry declaration
  `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrand_finite_module_card_eqStatement`
  reports that it has type `Prop`. Its axioms are only `propext`,
  `Classical.choice` and `Quot.sound`.
- A private audit module compiles an unmodified copy of the complete pinned
  source file beside this module. For each of the twenty-five theorems it
  checks in `MetaM` that:
  - the source declaration is a theorem and the target is a definition of type
    `Prop`;
  - the universe-parameter lists are identical;
  - the target's value is structurally equal (`Expr.equal`, which compares
    binder kinds) to the original theorem type. Before comparing, it renames
    original `CyclicCohomology.*` constants to
    `Langlands.NYLL.CyclicCohomology.*`, erases hygienic macro scopes from
    binder names, and inlines the auxiliary `_proof_N` lemmas that Lean
    abstracts out of a definition's value but not out of a theorem's type;
  - `protected` status and docstrings agree.

  Every constant of the source file that these types use is compared in the
  same way, recursively, with its adapted counterpart (see
  `Definitions.md`). All checks passed.

The private source copy and audit module are not part of this contribution.
They establish the correspondence during development and publish no proofs.

## Scope

These targets assert evaluation, kernel and cardinality facts about the norm
and `σ - 1` maps, the basic properties of the low-degree Herbrand quotient
groups `Ĥ⁰` and `Ĥ⁻¹`, vanishing criteria and their transport along
equivariant equivalences, and the equality of the two quotient cardinalities
for a finite module over a finite cyclic group. They do not assert
Herbrand-quotient multiplicativity in short exact sequences or any
class-formation, cup-product, Tate, transfer or reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
