# NYLL M117.018–M117.020 targets: finiteness and cardinality along `ModuleCat ℤ` isomorphisms

This module extracts three theorem types from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
Prop-valued definitions. It supplies targets only and contains no proofs of
them. Proofs are separate `lean.proof@1` work.

## Source

The original is
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`
(544 lines, SHA-256
`2757f501b1f901072b2292af5db735cc54db7f11b2403c3354a37f82fdda8226`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M117 (patch status "none in patch10").

The section context is source lines 19–35: `namespace CyclicCohomology`,
`noncomputable section`, `namespace ProfiniteCohomology`,
`namespace Herbrand`, `open CategoryTheory`, `variable {G A B C : Type}`
(line 28), an anonymous `section` (line 30, closed at line 365) and the
`variable` commands of lines 32–35:

```lean
variable [CommGroup G] [Fintype G]
variable [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]
```

There is no `omit`, `include` or `universe` command before line 363. None of
the three theorems mentions `G`, `A`, `B` or `C`, so Lean includes none of
these section variables (the instance arguments depend on them and are not
included either). Each theorem's telescope is exactly its own binder list.

## Exact source and parameter map

Original names are in `CyclicCohomology.ProfiniteCohomology.Herbrand`; target
names are in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
Append `Statement` to the original name to obtain the target's exact name.
Each target keeps the theorem's binders, in order and with their binder
kinds, as parameters of a definition whose type is `Prop`, and its body is
the theorem's asserted proposition.

| Unit | Original name; docstring / asserted type / proof lines | Paired Lean line | Parameters | Proposition |
| --- | --- | --- | --- | --- |
| M117.018 | `finite_source_of_moduleIso`; 341–342 / 343–345 / 346–347 | 38 | `{X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite Y]` | `Finite X` |
| M117.019 | `finite_target_of_moduleIso`; 349–350 / 351–353 / 354–355 | 45 | `{X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite X]` | `Finite Y` |
| M117.020 | `moduleCat_card_eq_of_iso`; 357–358 / 359–362 / 363 | 52 | `{X : ModuleCat.{0} ℤ} {T : Type} [CommGroup T] (e : X ≅ ModuleCat.of ℤ (Additive T))` | `Nat.card X = Nat.card T` |

Here `X ≅ Y` is an isomorphism in Mathlib's category `ModuleCat ℤ` of abelian
groups in universe `0`, and `Finite X` and `Nat.card X` refer to the
underlying type of `X`. M117.018 and M117.019 say that finiteness passes
along such an isomorphism in either direction. M117.020 says that an object
isomorphic to the additive form of a commutative group `T` has the
cardinality of `T` (as natural numbers, with `Nat.card` equal to `0` for
infinite types). All constructions are Mathlib's. No universe parameter
occurs.

## Modifications (Worker 5454)

- **Extraction**: only the asserted types are taken. The proofs (source lines
  346–347, 354–355 and 363) are omitted. The other declarations of the source
  file are not part of this module.
- **Form**: each theorem becomes a `def … : Prop` with the theorem's own
  parameters. Since no section variable is included, no `variable` command is
  needed, and none is used.
- **Linter**: in each target the isomorphism `e` does not occur in the
  proposition, so the unused-variable linter is disabled for each of the
  three definitions only,
  with `set_option linter.unusedVariables false in`. The premise names and
  types are unchanged.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
  `noncomputable section`, the nested namespaces and `open CategoryTheory` are
  kept. The anonymous `section` is not needed and is omitted.
- **Imports**: the source imports
  `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison` and
  `Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`
  (lines 7–8). The statements use only `ModuleCat`, `Finite` and `Nat.card`,
  so the port imports `Mathlib.Algebra.Category.ModuleCat.Basic` and
  `Mathlib.SetTheory.Cardinal.Finite` instead.
- **Docstrings**: the declaration docstrings are the source theorem
  docstrings. The module docstring is a modification notice.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection of each target
  reports that it returns `Prop`.
- A private audit module copies the three source theorems with their verbatim
  source proofs, in the source section context of lines 19–35 (including all
  the `variable` commands), into an auxiliary namespace nested in
  `Langlands.NYLL.CyclicCohomology`. A `MetaM` command then checks, for each
  theorem and its target, identical universe-parameter lists, identical
  binder names (after erasing hygienic macro scopes) and binder kinds along
  the whole telescope, and that the theorem's type is definitionally equal to
  `∀ xs, target xs`. All three passed, which also confirms that no section
  variable is included in the source theorems. As a control, a variant of
  the M115.001 target with its parameters `K` and `L` swapped was rejected by
  the same command.
- A second private module proves each target, applied to its parameters, by
  the verbatim source proof. Those proofs are not part of this contribution.

## Scope

These targets assert elementary transport of finiteness and cardinality along
isomorphisms. They do not assert a class-formation, cup-product, Tate,
transfer or reciprocity result, or the Herbrand cardinality identity of the
source file.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
