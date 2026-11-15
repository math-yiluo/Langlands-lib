# NYLL M145.003: the action by automorphisms on the quotient by a stable subgroup

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`.
The pinned source file has SHA-256
`5d4eeb8f1dc2a8efeef90ee3c9d89bb43c048d5057e49f32701cefc8768a05c6`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `LocalClassFieldTheory.` | Docstring | Attribute | Header | Body | Adapted name after `Langlands.NYLL.LocalClassFieldTheory.` |
| --- | --- | --- | --- | --- | --- | --- |
| M145.003 | `quotientMulDistribMulActionOfSubgroupStable` | 67–68 | 69 | 70–74 | 74–90 | `quotientMulDistribMulActionOfSubgroupStable` |

The source imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice`,
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic`,
`Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation` and
`Mathlib.GroupTheory.GroupAction.Quotient` (lines 7–10). The source context
is `namespace LocalClassFieldTheory` (line 16), `open LocalFieldTheory`
(line 18), `open CyclicCohomology` (line 20), `noncomputable section`
(line 22), `universe uG uA u` (line 24), `open scoped ValuativeRel`,
`open IsNonarchimedeanLocalField` and
`open CyclicCohomology.ProfiniteCohomology.Herbrand` (lines 26–28) and the
closing lines 293–294. The `variable` command of the source file (line 92)
comes after the definition, so the definition binds all of its parameters
itself and the telescope shown below is complete. The other declarations of
the source file are not part of this module; the two preceding ones,
M145.001 `subgroupMulDistribMulActionOfStable` and M145.002
`quotientActionOfSubgroupStable`, are already published.

The body uses the published theorem
`Langlands.NYLL.LocalClassFieldTheory.quotientActionOfSubgroupStable` (M145.002), in
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U002.Proofs`.
Its type is the published target
`quotientActionOfSubgroupStableStatement G A V hstable` of
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientActionStatement`,
which is by definition `MulAction.QuotientAction G V`. The source line
`letI : MulAction.QuotientAction G V := quotientActionOfSubgroupStable G A V hstable`
is therefore accepted unchanged: the ascribed type unfolds to the type of the
theorem, and the local instance is the same proof of the same Mathlib class.
Everything else is Mathlib: `Group`, `CommGroup`, `MulDistribMulAction`,
`Subgroup`, the quotient group `A ⧸ V` with `QuotientGroup.mk`, the class
`MulAction.QuotientAction` with the action of `G` on `A ⧸ V` that it
provides (from `Mathlib.GroupTheory.GroupAction.Quotient`),
`Quotient.inductionOn₂'`, `one_smul`, `mul_smul`,
`MulDistribMulAction.smul_mul`, `MulDistribMulAction.smul_one` and
`congrArg`.

## Definition

```lean
/-- Descend an action by group automorphisms to the quotient by an invariant
subgroup. -/
@[implicit_reducible]
def quotientMulDistribMulActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G (A ⧸ V) := by
  letI : MulAction.QuotientAction G V :=
    quotientActionOfSubgroupStable G A V hstable
  exact
    { smul := (· • ·)
      one_smul := one_smul G
      mul_smul := mul_smul
      smul_mul := by
        intro g x y
        refine Quotient.inductionOn₂' x y ?_
        intro a b
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_mul g a b)
      smul_one := by
        intro g
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_one g) }
```

For a group `G` acting by automorphisms on a commutative group `A` and a
subgroup `V` with `g • a ∈ V` whenever `a ∈ V`, the definition is the
action by automorphisms of `G` on `A ⧸ V` given by `g • [a] = [g • a]`. The
scalar multiplication, `one_smul` and `mul_smul` are those of the quotient
action provided by the local instance; the tactic blocks prove that it
respects products and the identity class. Like the source, it is a
definition with the attribute `@[implicit_reducible]`, not an instance, so
it adds no global instance.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.LocalClassFieldTheory.quotientMulDistribMulActionOfSubgroupStable`.
2. Copy the attribute, the docstring, the binders and the body verbatim,
   with the source line breaks; the reference to
   `quotientActionOfSubgroupStable` now resolves to the published M145.002.
3. Replace the four source imports by
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U002.Proofs`,
   which publishes M145.002 and imports
   `Mathlib.GroupTheory.GroupAction.Quotient`, and the source module
   docstring by a description of this module with a modification notice.
4. Omit the five source `open` commands (lines 18, 20 and 26–28) and the
   universe `u` of line 24: the definition uses no name of those namespaces,
   no `ValuativeRel` notation and no universe `u`, so its elaboration is
   unchanged. Keep the namespace, the noncomputable section and the
   universes `uG uA`. Omit the other declarations of the source file.
5. No helper declaration, instance or linter option is added.

This is a definition only. It discharges no host class-formation, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
