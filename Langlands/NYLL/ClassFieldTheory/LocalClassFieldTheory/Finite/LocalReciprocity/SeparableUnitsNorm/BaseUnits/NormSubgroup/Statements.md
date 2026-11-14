# The finite norm subgroup of separable-closure units: comparison target

The paired Lean file extracts one proposition from Naganori Yamaguchi's
ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`
(SHA-256 `b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The inventory `notes/reuse/nyll-public-port/m073-m096.md`, section M096,
records no patch10 modification of this source file. No applicable NYLL
erratum was found in the Library's `notes/errata/`.

## Exact source correspondence

| Unit and source lines | Original theorem | Adapted proposition definition |
| --- | --- | --- |
| M096.007; docstring 188–189, theorem type 190–195, proof 195–226 | `LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroup` | `Langlands.NYLL.LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroupStatement` |

The definition keeps the complete source parameter telescope from
lines 36–37 and 62, in order:

```lean
(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
(E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
```

The source theorem has no further binders. The fields and the intermediate
field are explicit. Both field types are in universe zero, and the
declaration has no universe parameters. Both Galois hypotheses and the
finite-dimensional hypothesis are kept. The source has no `omit` command
before this theorem. The ambient extension `Ω / K` may be infinite. There
is no perfectness, valuation or local-field hypothesis.

## Proposition and meaning

The body is the source proposition, character for character, with its names
resolved in `Langlands.NYLL`:

```lean
(finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
  (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
  (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).map
    (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
  additiveNormSubgroup K E
```

Here is what each part means:

- `galoisAmbientUnitsRep K Ω` (published M088.001) is the actual integral
  representation `Rep.ofAlgebraAutOnUnits K Ω` of `Gal(Ω/K)` on
  `Additive Ωˣ`.
- `closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)` and
  `closedFixingSubgroup K Ω E` are the closed subgroups fixing `K` and `E`.
  `fixingSubgroupLeBase K Ω E` is the published proof that the second lies
  in the first.
- `finiteNormSubgroup A K L hLK` (published M039.001) is the range of the
  abstract relative norm `relativeNorm A K L hLK`. Here the norm runs from
  the units fixed by the fixing subgroup of `E` to the units fixed by the
  fixing subgroup of the bottom field, which is all of `Gal(Ω/K)`. So this
  left argument is an additive subgroup of the units of `Ω` fixed by
  `Gal(Ω/K)`.
- `baseUnitsEquivGaloisAmbientFixed K Ω` (published M096.001) is the actual
  additive equivalence from `Additive Kˣ` to those fixed coefficients. The
  image of the norm subgroup under its inverse is an additive subgroup of
  `Additive Kˣ`.
- `additiveNormSubgroup K E` (published M095.008) is the additive form of
  `localNormSubgroup K E = (normUnits K E).range`. This is the ordinary norm
  group `N_{E/K}(Eˣ)`, with `normUnits` the restriction of `Algebra.norm K`
  to units.

So the proposition says that, when the base fixed units are identified with
`Kˣ`, the abstract finite norm subgroup is exactly the ordinary field-norm
subgroup of `E / K`. Both sides are subgroups of `Additive Kˣ`, and the
equality is equality of additive subgroups. The source proof is omitted; the
paired Lean file only defines the proposition and does not prove it.

## Reuse, finiteness and modifications

The focused imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions`,
  which supplies M096.001 and, through its imports, the M088.006
  intermediate-field equivalence, `galoisAmbientUnitsRep` and
  `closedFixingSubgroup`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions`,
  which supplies the published instance
  `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite`
  (M096.003) and, through its imports, `fixingSubgroupLeBase`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`,
  which supplies published M039.001 `Langlands.NYLL.ClassFormation.finiteNormSubgroup`
  and, through its imports, `relativeNorm`;
- `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions`,
  which supplies published M095.008
  `Langlands.NYLL.CyclicCohomology.additiveNormSubgroup`.

`finiteNormSubgroup` needs the quotient of the base fixing subgroup by
`(closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
  (closedFixingSubgroup K Ω ⊥).toSubgroup`
to be finite. The source instance M096.003 is stated with
`extensionSubgroup`, and the published `extensionSubgroup` abbreviation is
exactly this `subgroupOf`. So typeclass inference finds the existing
instance from the source hypotheses. No instance, alternative norm, norm
subgroup or local copy of a sibling definition is introduced. All four
definitions above are used by their published Lean names; none is replaced by
an assumed map or an arbitrary coefficient group.

Worker 62 made these changes on 14 November 2026:

- extracted only M096.007 into this focused module;
- prefixed `LocalClassFieldTheory` with `Langlands.NYLL`;
- changed the `theorem` to a `def` returning `Prop` and appended
  `Statement` to its name;
- omitted the source proof;
- replaced the source docstring with a description of the proposition;
- replaced the broad source imports and the file introduction with the
  focused imports and a modification notice;
- merged the source namespace openings into one line and left out the unused
  `BigOperators` scope.

The `noncomputable section`, the `FiniteGaloisIntermediate` section, and the
source parameter declarations and their order are unchanged. No subgroup,
map, coercion, binder kind or hypothesis is changed. No existing Library or
Mathlib declaration states this comparison.

## Development checks

A focused `lean_check` inspection in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, over Library commit
`58ad0f796899b4aa457077d0146815c24758f739` (diagnostic
`af1c3429-681a-419c-b230-216d4c1f5224`), succeeded with zero errors and zero
warnings. It reports `statement_returns_prop: true`, an empty
universe-parameter list, and only the axioms `propext`, `Classical.choice`
and `Quot.sound`. This is a development check. Independent acceptance and
publication are separate requirements.

## Attribution and scope

The Lean file keeps the original copyright, author and Apache-2.0 header
word for word. The published `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` keep the original license and notices. Worker 62's
extraction and changes are recorded above and in the Lean header. This file
is a support statement target only. It does not prove the comparison and it
discharges no host class-formation, reciprocity or norm-quotient target.
