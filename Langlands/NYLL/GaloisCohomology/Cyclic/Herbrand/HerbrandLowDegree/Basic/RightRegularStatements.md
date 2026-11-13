# NYLL M113 targets: right-regular cyclic partial products, cyclic index, cyclic primitive and transport equivariance

This module extracts ten theorem types from Naganori Yamaguchi's
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

- *rr* for `{G : Type uG} {B : Type uB} [Group G] [CommGroup B]` (the `omit`
  removes `[Fintype G]`, `[CommGroup A]`, `[CommGroup C]` and the three
  actions);
- *index* for `{G : Type uG} [Group G] [Fintype G]` (the `omit` removes the
  three `CommGroup` instances and the three actions);
- *finite rr* for `{G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]`
  (the `omit` removes `[CommGroup A]`, `[CommGroup C]` and the three actions);
- `P` for `rightRegularCyclicPartialProduct (G := G) (B := B)`, `I` for
  `rightRegularCyclicIndex (G := G)` and `Q` for
  `rightRegularCyclicPrimitive (G := G) (B := B)`, and *hgen* for
  `(hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)`.

These abbreviations describe the table only. The Lean definitions spell out
every binder and every term.

| Unit | Original name; `omit` / docstring / asserted type lines | Paired Lean line | Complete telescope | Conclusion |
| --- | --- | --- | --- | --- |
| M113.082 | `rightRegularCyclicPartialProduct_succ`; 1046–1048 / 1049 / 1050–1052 | 37 | rr; `(σ : G) (f : G → B) (i : ℕ)` | `P σ f (i + 1) = P σ f i * f (σ ^ i)` |
| M113.083 | `rightRegularCyclicPartialProduct_succ_mul_inv`; 1055–1057 / 1058–1059 / 1060–1064 | 45 | rr; `(σ : G) (f : G → B) (i : ℕ)` | `P σ f (i + 1) * (P σ f i)⁻¹ = f (σ ^ i)` |
| M113.084 | `rightRegularCyclicPartialProduct_wrap_mul_inv_of_eq_one`; 1068–1070 / 1071–1072 / 1073–1078 | 56 | rr; `(σ : G) (f : G → B) {n : ℕ} (hn : 0 < n) (hprod : P σ f n = 1)` | `P σ f 0 * (P σ f (n - 1))⁻¹ = f (σ ^ (n - 1))` |
| M113.086 | `rightRegularCyclicIndex_spec`; 1100–1102 / 1103 / 1104–1106 | 65 | index; `(σ : G)` hgen `(x : G)` | `x = σ ^ (I σ hgen x).val` |
| M113.087 | `rightRegularCyclicIndex_eq_of_repr`; 1110–1112 / 1113–1114 / 1115–1118 | 73 | index; `(σ : G)` hgen `{x : G} {m : ZMod (Fintype.card G)} (hm : x = σ ^ m.val)` | `I σ hgen x = m` |
| M113.088 | `rightRegularCyclicIndex_val_pow_of_lt`; 1121–1123 / 1124–1125 / 1126–1129 | 82 | index; `(σ : G)` hgen `{i : ℕ} (hi : i < Fintype.card G)` | `(I σ hgen (σ ^ i)).val = i` |
| M113.090 | `rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_succ_lt`; 1148–1150 / 1151–1152 / 1153–1158 | 91 | finite rr; `(σ : G)` hgen `(f : G → B) (x : G) (hix : (I σ hgen x).val + 1 < Fintype.card G)` | `Q σ hgen f (x * σ) * (Q σ hgen f x)⁻¹ = f x` |
| M113.091 | `rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_eq_card_sub_one`; 1179–1181 / 1182–1183 / 1184–1191 | 102 | finite rr; `(σ : G)` hgen `(f : G → B) (x : G) (hix : (I σ hgen x).val = Fintype.card G - 1) (hprod : P σ f (Fintype.card G) = 1)` | `Q σ hgen f (x * σ) * (Q σ hgen f x)⁻¹ = f x` |
| M113.092 | `rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_partialProduct_eq_one`; 1234–1236 / 1237–1238 / 1239–1246 | 115 | finite rr; `(σ : G)` hgen `(f : G → B) (hprod : P σ f (Fintype.card G) = 1) (x : G)` | `Q σ hgen f (x * σ) * (Q σ hgen f x)⁻¹ = f x` |
| M113.104 | `mulEquivRightRegularFunctionOfAddEquiv_commutes`; 1559–1561 / 1562–1563 / 1564–1572 | 128 | `{G : Type uG} [Group G]` (the `omit` removes `[Fintype G]`, the `CommGroup` instances and the actions); `{M : Type uA} {D : Type uB} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D] (e : M ≃+ (G → D)) (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g)) (g : G) (m : Multiplicative M) (x : G)` | `letI := multiplicativeMulDistribMulActionOfDistribMulAction G M` followed by `mulEquivRightRegularFunctionOfAddEquiv G e (g • m) x = mulEquivRightRegularFunctionOfAddEquiv G e m (x * g)` |

Meaning of the targets. `P σ f i` is the partial product
`f (σ ^ 0) * ⋯ * f (σ ^ (i - 1))`. `I σ hgen x` is the unique
`n : ZMod |G|` with `x = σ ^ n.val`, and `Q σ hgen f x = P σ f (I σ hgen x).val`.
M113.082–M113.084 are the successor and wrap-around identities of the partial
products. M113.086–M113.088 characterize the chosen index. M113.090–M113.092
say that `b = Q σ hgen f` satisfies `b (x * σ) * (b x)⁻¹ = f x`: at an index
below `|G| - 1` unconditionally, and at the last index and then everywhere
when the full-period product `P σ f |G|` is `1`. Under the right-regular action
`(g • b) x = b (x * g)` of M113.009, `b (x * σ) * (b x)⁻¹` is the value at `x`
of `sigmaMinusOne G (G → B) σ b`; a private check confirms this by `rfl`. The
targets themselves are stated pointwise, exactly as in the source. M113.104
says that the multiplicative equivalence M113.103 intertwines the
multiplicative wrapper of the given `G`-action on `M` (M113.101, installed
locally with `letI`) with the right-regular action on functions, assuming the
additive equivalence `e` does so pointwise (`he`).

The definitions close the entire elaborated source telescope inside `∀`, so
each declaration type is `Prop`. Braces, parentheses and instance brackets
keep their source binder kinds. The proof premises `hn`, `hprod`, `hgen`,
`hm`, `hi`, `hix` and `he` remain named explicit binders with their source
types. The unused-variable linter is disabled locally, with
`set_option linter.unusedVariables false in`, only for the seven definitions
whose named premises do not occur in their conclusions: M113.084, M113.087,
M113.088, M113.090, M113.091, M113.092 and M113.104.

`rightRegularCyclicPartialProduct`, `rightRegularCyclicIndex`,
`rightRegularCyclicPrimitive`, `multiplicativeMulDistribMulActionOfDistribMulAction`
and `mulEquivRightRegularFunctionOfAddEquiv` are the actual constructions of
the sibling `RightRegularDefinitions` module (M113.080, M113.085, M113.089,
M113.101 and M113.103). `Subgroup.zpowers`, `ZMod`, `ZMod.val`,
`Fintype.card`, `Multiplicative` and `AddEquiv` are Mathlib's.

## Modifications (Worker 5086)

- **Extraction**: only the asserted types are taken. Every proof body (for
  example source lines 1053, 1079–1088 and 1192–1232) is omitted.
  M113.081 `rightRegularCyclicPartialProduct_zero` is not in the task list and
  is not part of this module.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
- **Section variables**: written as explicit `∀` binders in the order of lines
  62–64, followed by each theorem's own binders. No `variable` or `omit`
  command is used.
- **Imports**: the sole import is the sibling module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.RightRegularDefinitions`,
  which imports `Basic.Definitions` and through it the source's nine Mathlib
  imports. Nothing is redefined here.
- **Docstrings**: the declaration docstrings are the source theorem
  docstrings. The module docstring is a modification notice. A comment records
  why the linter is disabled.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module compiles an unmodified copy of the complete pinned
  source file beside this module. For each of the ten theorems it checks in
  `MetaM` that the theorem and its target have identical universe-parameter
  lists, that the target's type is `Prop`, and that the target's value is
  structurally equal (`Expr.equal`, which compares binder kinds) to the
  original theorem type. Before comparing, it renames original
  `CyclicCohomology.*` constants to `Langlands.NYLL.CyclicCohomology.*` and
  erases hygienic macro scopes from binder names. It also checks with
  `isDefEq` that each unapplied target constant is definitionally equal to the
  type of the original theorem constant at the same universe parameters. All
  ten checks passed. The universe parameters are `uG uB` for M113.082–M113.084
  and M113.090–M113.092, `uG` for M113.086–M113.088 and `uG uA uB` for
  M113.104.

The private source copy and audit module are not part of this contribution.
They establish the correspondence during development and publish no proofs.

## Scope

These targets assert elementary identities for finite products along the
powers of a generator, the chosen cyclic index, the cyclic primitive of the
right-regular module and the equivariance of a transport equivalence. They do
not assert a class-formation, cup-product, Tate, transfer or reciprocity
result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
