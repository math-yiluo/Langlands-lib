# NYLL M084.001: the fixed corrected combination

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_fixedCombination_of_commuteStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_fixedCombination_of_commute`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractReciprocity_fixedCombination_of_commuteStatement B g t hcomm c b a htc hgb hbc`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has the implicit group `Q : IntegralRepGroupType` (that is,
`Type 0`) with `[Group Q]`, and, in this order, the explicit integral
representation `B : Rep ℤ Q`, group elements `g t : Q`, the hypothesis
`hcomm : Commute g t`, vectors `c b a : B.V`, and the hypotheses

- `htc : B.ρ t c = c` (`t` fixes `c`),
- `hgb : B.ρ g b = B.ρ t b` (`g` and `t` agree on `b`),
- `hbc : b - c = B.ρ g a - a` (`b - c` is the `g`-coboundary of `a`).

Like the statement, the theorem has one universe parameter, the carrier
universe of `B`.

Unfolding the published proposition gives

```lean
B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a
```

that is, the corrected combination `b + a - t·a` is fixed by `g`.

## Implemented proof

The proof is the source's elementary calculation in the abelian group
`B.V`, using that each `B.ρ x` is additive.

1. `hcommAction : B.ρ g (B.ρ t a) = B.ρ t (B.ρ g a)`. By `map_mul` for the
   monoid homomorphism `B.ρ`, the left side equals `B.ρ (g * t) a` and the
   right side equals `B.ρ (t * g) a` (after `rw [map_mul]` the remaining
   goals close by `rfl`, since applying a product of linear endomorphisms is
   applying them in turn), and these agree by rewriting with
   `hcomm.eq : g * t = t * g`.
2. `hb : b = c + B.ρ g a - a`, from `hbc` by `abel` and rewriting.
3. Applying `B.ρ t` to `hbc` (`congrArg`) and simplifying with `map_sub` and
   `htc` gives `htbc' : B.ρ t b - c = B.ρ t (B.ρ g a) - B.ρ t a`, hence
   `htb : B.ρ t b = c + B.ρ t (B.ρ g a) - B.ρ t a` by `abel`.
4. The final `calc` chain computes
   `B.ρ g (b + a - B.ρ t a) = B.ρ g b + B.ρ g a - B.ρ g (B.ρ t a)`
   (`simp only [map_add, map_sub]`),
   `= B.ρ t b + B.ρ g a - B.ρ t (B.ρ g a)` (rewriting with `hgb` and
   `hcommAction`), `= c + B.ρ g a - B.ρ t a` (rewriting with `htb`, then
   `abel`), `= b + a - B.ρ t a` (rewriting with `hb`, then `abel`).

The `calc` chain proves the unfolded equality, which Lean accepts for the
goal stated through the published proposition by definitional unfolding.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring. No auxiliary
declaration, extra hypothesis or instance is introduced. The development
check reports no errors or warnings, one universe parameter, and only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocity_fixedCombination_of_commuteStatement`
  in Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.Statements,
  and the universe abbreviation `IntegralRepGroupType`
  (`Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`) reached
  through it.
- Mathlib's `Rep`, `map_mul`, `map_add`, `map_sub`, `Commute.eq`,
  `congrArg`, and the `abel`, `simp only`, `simpa`, `rw` and `calc` tactics,
  available through the Statements module's import of
  `Mathlib.RepresentationTheory.Rep.Basic`.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:29–67`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean#L29-L67).
Lines 29–30 are the docstring, 31–37 the signature and 38–67 the proof.
The file opens `noncomputable section` (line 19) and
`namespace ClassFormation` (21), with `open KummerTheory` (23),
`open CyclicCohomology` (24), and the section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (27, with the
comment on line 26), which this theorem does not use. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m084)
places this proof at M084.001 (source unit lines 31–70). The whole-file
SHA-256 is
`4c8289dbb89fb3459f1248a4cd171f813fdc5e7bcba9e845d8b1929261f40f50`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_fixedCombination_of_commute` (M084.001) | Published `abstractReciprocity_fixedCombination_of_commuteStatement` in Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.Statements |
| Proof `abstractReciprocity_fixedCombination_of_commute` | This theorem of the same adapted name in Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.U001.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, keeps the
`noncomputable section` and the docstring, omits the unused `open` lines and
the unused section variables for `G` with their comment, and states the
theorem's type as the published proposition applied to
`B g t hcomm c b a htc hgb hbc`. The proof is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M084.001. The later FixedSource units M084.002
onward and any host class-formation, cup, transfer, Tate or reciprocity
target are separate work.
