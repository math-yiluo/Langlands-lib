# NYLL M113 targets: right-regular norm kernel and augmentation subgroup, and vanishing of the low-degree Herbrand quotients of induced modules

This module extracts nine theorem types from Naganori Yamaguchi's
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
Each theorem includes the variables that remain after its `omit … in` and
that its statement mentions, together with the remaining instance variables
whose types mention only included variables. They come first, in the order of
lines 62–64. In the table, write

- *finite rr* for `{G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]`
  (the `omit` removes `[CommGroup A]`, `[CommGroup C]` and the three actions);
- *rr* for `{G : Type uG} {B : Type uB} [Group G] [CommGroup B]` (the `omit`
  also removes `[Fintype G]`);
- *transport* for `{G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G] [CommGroup A] [CommGroup B] [MulDistribMulAction G A]`
  (the `omit` removes `[CommGroup C]` and the actions on `B` and `C`);
- *additive* for `{G : Type uG} [Group G] [Fintype G]` (the `omit` removes the
  three `CommGroup` instances and the three actions; `A` and `B` are not
  mentioned), followed by the theorem's own
  `{M : Type uA} {D : Type uB} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]`;
- *hgen* for `(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)`.

These abbreviations describe the table only. The Lean definitions spell out
every binder and every term.

| Unit | Original name; `omit` / docstring / asserted type lines | Paired Lean line | Complete telescope | Conclusion |
| --- | --- | --- | --- | --- |
| M113.079 | `rightRegularFunction_mem_normKernelSubgroup_iff`; 984–986 / 987–988 / 989–991 | 40 | finite rr; `(f : G → B)` | `f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ↔ (∏ g : G, f g) = 1` |
| M113.093 | `rightRegularFunction_prod_powers_eq_one_of_mem_normKernel`; 1263–1265 / 1266–1267 / 1268–1272 | 50 | finite rr; `(σ : G)` hgen `{f : G → B} (hf : f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B))` | `(Finset.range (Nat.card G)).prod (fun i => f (σ ^ i)) = 1` |
| M113.094 | `rightRegularFunction_mem_augmentationSubgroup_iff`; 1296–1298 / 1299–1300 / 1301–1304 | 59 | rr; `(σ : G) (f : G → B)` | `f ∈ rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ ↔ ∃ b : G → B, ∀ x : G, b (x * σ) * (b x)⁻¹ = f x` |
| M113.095 | `rightRegularFunction_normKernel_le_augmentationSubgroup`; 1322–1324 / 1325–1326 / 1327–1330 | 68 | finite rr; `(σ : G)` hgen | `rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ≤ rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ` |
| M113.097 | `rightRegularFunction_fixed_le_tateNormSubgroup`; 1359–1361 / 1362–1363 / 1364–1366 | 76 | finite rr | `rightRegularFunctionFixedSubgroup (G := G) (B := B) ≤ rightRegularFunctionTateNormSubgroup (G := G) (B := B)` |
| M113.099 | `herbrandH0_subsingleton_of_equiv_rightRegularFunction`; 1429 / 1430–1431 / 1432–1435 | 84 | transport; `(e : A ≃* (G → B)) (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g))` | `Subsingleton (HerbrandH0 G A)` |
| M113.100 | `herbrandHMinusOne_subsingleton_of_equiv_rightRegularFunction`; 1446 / 1447–1448 / 1449–1453 | 94 | transport; `(σ : G)` hgen `(e : A ≃* (G → B)) (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g))` | `Subsingleton (HerbrandHMinusOne G A σ)` |
| M113.105 | `herbrandH0_subsingleton_of_addEquiv_rightRegularFunction`; 1577–1579 / 1580–1581 / 1582–1588 | 105 | additive; `(e : M ≃+ (G → D)) (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g))` | `letI := multiplicativeMulDistribMulActionOfDistribMulAction G M` followed by `Subsingleton (HerbrandH0 G (Multiplicative M))` |
| M113.106 | `herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunction`; 1613–1615 / 1616–1617 / 1618–1625 | 117 | additive; `(σ : G)` hgen `(e : M ≃+ (G → D)) (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g))` | `letI := multiplicativeMulDistribMulActionOfDistribMulAction G M` followed by `Subsingleton (HerbrandHMinusOne G (Multiplicative M) σ)` |

M113.105 and M113.106 reuse the universe names `uA` and `uB` for their own
types `M` and `D`, as in the source. Their universe parameters are
`uG uA uB`.

The definitions close the entire elaborated source telescope inside `∀`, so
each declaration type is `Prop`. Braces, parentheses and instance brackets
keep their source binder kinds, and every hypothesis keeps its source name,
type and position. The unused-variable linter is disabled locally, with
`set_option linter.unusedVariables false in` and a comment, only for the six
definitions whose named premises do not occur in their conclusions: M113.093,
M113.095, M113.099, M113.100, M113.105 and M113.106.

## Meaning of the targets

`rightRegularFunctionTateNormSubgroup` (M113.059),
`rightRegularFunctionNormKernelSubgroup` (M113.062) and
`rightRegularFunctionAugmentationSubgroup` (M113.063) are the constructions
of the sibling module `Definitions.lean`, and `HerbrandH0` and
`HerbrandHMinusOne` (M113.028, M113.029) are the low-degree Herbrand quotient
groups defined there. `rightRegularFunctionFixedSubgroup` (M113.058) and
`multiplicativeMulDistribMulActionOfDistribMulAction` (M113.101) are the
published constructions of `Basic.RightRegularDefinitions`. The four
right-regular subgroups are `fixedSubgroup`, `tateNormSubgroup`,
`normKernelSubgroup` and `augmentationSubgroup` of `G → B` under the
right-regular action `(g • f) x = f (x * g)` of M113.009 (`Basic.Definitions`),
installed locally with `letI`. M113.101 makes `Multiplicative M` a
multiplicative `G`-module from an additive one.

- M113.079: under the right-regular action, `f` lies in the norm kernel
  exactly when `∏ g : G, f g = 1`.
- M113.093: if `σ` generates `G` and `f` lies in the norm kernel, the product
  of `f (σ ^ i)` over `i < Nat.card G` is `1`.
- M113.094: `f` lies in `(σ - 1)(G → B)` exactly when
  `f x = b (x * σ) * (b x)⁻¹` for some `b : G → B` and all `x`.
- M113.095: if `σ` generates `G`, the norm kernel lies in `(σ - 1)(G → B)`;
  this is the vanishing of `Ĥ⁻¹` for the right-regular module.
- M113.097: every fixed point of `G → B` is a norm; this is the vanishing of
  `Ĥ⁰`.
- M113.099 and M113.100: if `e : A ≃* (G → B)` intertwines the action on `A`
  with the right-regular action, then `HerbrandH0 G A` is a subsingleton,
  and, for a generator `σ`, so is `HerbrandHMinusOne G A σ`.
- M113.105 and M113.106: the same for an additive `G`-module `M` with an
  additive equivalence `e : M ≃+ (G → D)` intertwining the actions, viewed
  multiplicatively as `Multiplicative M` with the action of M113.101.

## Modifications (Worker 9)

- **Extraction**: only the asserted types are taken. Every proof body is
  omitted. None of the nine source theorems carries an attribute or a
  `protected` or `private` modifier.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
- **Section variables**: written as explicit `∀` binders in the order of lines
  62–64, followed by each theorem's own binders. No `variable` or `omit`
  command is used.
- **`letI` in the asserted type**: the source types of M113.105 and M113.106
  begin with `letI := multiplicativeMulDistribMulActionOfDistribMulAction G M`.
  The targets keep it unchanged after the binders.
- **Imports**: the sibling module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`
  and the published module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.RightRegularDefinitions`.
  Through them the source's nine Mathlib imports are available. Nothing is
  redefined here.
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
  `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandH0_subsingleton_of_equiv_rightRegularFunctionStatement`
  reports that it has type `Prop`. Its axioms are only `propext`,
  `Classical.choice` and `Quot.sound`.
- A private audit module compiles an unmodified copy of the complete pinned
  source file beside this module. For each of the nine theorems it checks in
  `MetaM` that:
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

  Every constant of the source file that these types use, including
  M113.058, M113.059, M113.062, M113.063 and M113.101, is compared in the
  same way, recursively, with its adapted counterpart (see `Definitions.md`).
  All checks passed.

The private source copy and audit module are not part of this contribution.
They establish the correspondence during development and publish no proofs.

## Scope

These targets describe the norm kernel and the `σ - 1` image of the
right-regular module `G → B`, assert that its low-degree Herbrand quotients
vanish, and transport that vanishing to modules isomorphic to it,
multiplicatively or additively. They do not assert vanishing for modules
induced from a nontrivial subgroup, Shapiro's lemma, Herbrand-quotient
multiplicativity, or any class-formation, cup-product, Tate, transfer or
reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
