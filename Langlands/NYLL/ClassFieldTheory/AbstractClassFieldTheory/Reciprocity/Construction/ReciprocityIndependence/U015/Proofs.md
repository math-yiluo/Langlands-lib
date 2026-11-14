# NYLL M033.015: finite extensions between finite intermediate fields

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.finite_extension_of_leStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.finite_extension_of_le`.
The theorem's type is exactly that proposition applied to its source
parameters, `finite_extension_of_leStatement hPK hMK hPM`, with the
finiteness instance `hPfinite` passed by instance resolution.

Its target import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.U015.Statements`
([`Statements.lean`](Statements.lean)). That published Lean/Markdown pair and
everything it imports are unchanged.

## Target and parameters

At universe `u`, the theorem has, in this order:

1. implicit `{G : Type u}` with instances `[Group G] [TopologicalSpace G]`
   (the section variable line of the source);
2. implicit `{P M K : ClosedSubgroup G}`;
3. explicit `hPK : P.toSubgroup ≤ K.toSubgroup`,
   `hMK : M.toSubgroup ≤ K.toSubgroup` and
   `hPM : P.toSubgroup ≤ M.toSubgroup`;
4. the instance
   `[hPfinite : Finite (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)]`.

The published proposition is an application of the M040.025 target
`FiniteGaloisSubextension.finite_extension_over_intermediateStatement` to
these parameters. Unfolding both definitions and the abbreviation
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002, whose body is
`L.toSubgroup.subgroupOf K.toSubgroup`) gives

```lean
Finite (M.toSubgroup ⧸ P.toSubgroup.subgroupOf M.toSubgroup)
```

So if `P` has finite index in `K` and `P ≤ M ≤ K`, then `P` has finite index
in `M`. In the source's field language, a finite extension `P | K` stays finite
over the intermediate field `M`. These are coset spaces. No normality,
topological group law or profiniteness is used.

## Implemented proof

The proof applies the existing M040.025 theorem `FiniteGaloisSubextension.finite_extension_over_intermediate hPK hMK hPM`, imported from `FiniteGaloisSubextension.U025.Proofs`. Its target is definitionally the required proposition. The original source argument, also implemented by that existing theorem, is recorded below; integration reuses it without repeating its implementation.

1. `show Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM)` replaces the
   goal by the source conclusion. It is definitionally equal to the
   proposition through the two Statement definitions and the
   `extensionSubgroup` abbreviation.
2. `hPKindex : P.toSubgroup.relIndex K.toSubgroup ≠ 0`. After
   `rw [Subgroup.relIndex]` the goal is
   `(P.toSubgroup.subgroupOf K.toSubgroup).index ≠ 0`. It is closed by
   Mathlib's `Subgroup.index_ne_zero_of_finite` at the group `K.toSubgroup`
   and the subgroup `extensionSubgroup K P hPK`, with the finiteness instance
   given explicitly as `hPfinite`.
3. `hPMindex : P.toSubgroup.relIndex M.toSubgroup ≠ 0`. Assume it is zero.
   Mathlib's `Subgroup.relIndex_mul_relIndex` with `hPM` and `hMK` gives
   `P.relIndex M * M.relIndex K = P.relIndex K`. Rewriting with the
   assumption and `zero_mul` turns this into `0 = P.relIndex K`, which
   contradicts `hPKindex`.
4. `apply Nat.finite_of_card_ne_zero` reduces the goal to
   `Nat.card (M.toSubgroup ⧸ extensionSubgroup M P hPM) ≠ 0`.
   `change (extensionSubgroup M P hPM).index ≠ 0` restates this through
   Mathlib's definition `Subgroup.index H = Nat.card (G ⧸ H)`.
5. `simpa [Subgroup.relIndex] using hPMindex` closes it, since
   `P.relIndex M` unfolds to the index of `P.toSubgroup.subgroupOf M.toSubgroup`.

The development check of this module reports no errors or warnings. The
theorem has universe parameter `u`, and its axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.FiniteIntermediateField.finite_extension_of_leStatement`
  and, through its body, the published M040.025 proposition
  `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediateStatement`.
  Both are used only by definitional unfolding.
- The published abbreviation `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  (M004.002), reached through the import chain and opened in the file.
- Mathlib's `Subgroup.index` and `Subgroup.relIndex` (definitions,
  `Mathlib/GroupTheory/Index.lean`, lines 57–58 and 64–65),
  `Subgroup.relIndex_mul_relIndex` (line 127),
  `Subgroup.index_ne_zero_of_finite` (line 533), `Nat.finite_of_card_ne_zero`
  (`Mathlib/SetTheory/Cardinal/Finite.lean`, line 89) and `zero_mul`. Line
  numbers refer to Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The proof directly reuses the published M040.025 theorem. The Mathlib results above are its underlying finite-index argument; no host class-formation, cup, transfer, Tate or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:247–269`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean#L247-L269).
Lines 247–248 are the docstring, 249–256 the signature and 257–269 the
proof. The theorem lies in `namespace ClassFormation` (line 19, with
`open KummerTheory` and `open CyclicCohomology` at lines 21 and 23), the
`noncomputable section`, `section groupTheoreticRefinements` (line 29) with
the variable line 31 `{G : Type u} [Group G] [TopologicalSpace G]`, and
`namespace FiniteIntermediateField` (lines 33–271). The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m033)
lists this theorem as M033.015 (source unit from line 249; the next unit
starts at line 278). The whole-file SHA-256 is
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation.FiniteIntermediateField` | Adapted in `Langlands.NYLL.ClassFormation.FiniteIntermediateField` |
| --- | --- |
| Asserted type of `finite_extension_of_le` (M033.015) | Published `finite_extension_of_leStatement` in ReciprocityIndependence.U015.Statements |
| Proof `finite_extension_of_le` | This theorem of the same adapted name in ReciprocityIndependence.U015.Proofs |

Worker 395 made these source-extraction changes on 14 November 2026 UTC; integration subsequently reuses M040.025 as described above:

- prefix the namespace with `Langlands.NYLL`;
- replace the two source imports by the sole published Statements import;
- state the theorem's type as the published proposition applied to
  `hPK hMK hPM`, with `hPfinite` resolved as an instance;
- write the instance type with `P.toSubgroup.subgroupOf K.toSubgroup`, the
  body of the source's `extensionSubgroup K P hPK`, as the published
  statement does;
- add the leading `show` that unfolds the proposition to the source
  conclusion;
- open `Langlands.NYLL.CyclicCohomology` so that the source proof's
  `extensionSubgroup` resolves to the published abbreviation, and omit the
  unused `open KummerTheory`;
- omit the section name `groupTheoreticRefinements` and the other
  declarations of the source sections.

The universe, the variable line, the `noncomputable section`, the docstring,
the theorem name, and the binders and their names and order are unchanged. The integrated proof uses the already published theorem with the same mathematical proposition.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors. Worker 353's statement is used unchanged.

The unchanged inherited
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the Lake
build, kernel and exact-target checks, unchanged statement and dependency
checks, independent semantic review and Integrator publication.

This proof covers only M033.015. It does not prove the M040.025 theorem
`FiniteGaloisSubextension.finite_extension_over_intermediate` under its own
name, and it is not a class-formation, cup, transfer, Tate or reciprocity
result.
