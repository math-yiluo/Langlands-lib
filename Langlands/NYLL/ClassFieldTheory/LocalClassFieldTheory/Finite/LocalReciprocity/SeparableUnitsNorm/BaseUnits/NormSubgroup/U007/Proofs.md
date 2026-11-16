# NYLL M096.007: finite norm subgroup comparison

The paired Lean file proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroupStatement K Ω E`
under the required name
`Langlands.NYLL.LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroup`.
The statement and its dependencies are unchanged.

The complete telescope is
`(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]`
followed by `(E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]`.
Both fields are in universe zero. The ambient Galois extension may be
infinite. No separable-closedness, valuation, topology on the fields or
local-field assumption is added.

## Implemented proof

After unfolding the named proposition, `ext y; constructor` reduces the
subgroup equality to the two membership implications, as in the source.

For an element of the mapped finite norm subgroup, extract its abstract
relative-norm witness `b`. The inverse of
`intermediateFieldUnitsEquivGaloisFixed K Ω E` supplies a unit `u : Eˣ`
representing `b`. Rewrite by the private norm comparison, then cancel the
base-unit equivalence with its inverse. The resulting element is the
ordinary field norm of `u`, which is a witness in `additiveNormSubgroup`.

Conversely, extract a unit `u : Eˣ` witnessing membership in the ordinary
norm subgroup. Use the base fixed coefficient of `normUnits K E u` as the
image witness, and the fixed coefficient of `u` as its abstract norm
preimage. The private comparison proves that this is a valid preimage;
canceling the equivalence proves the required image equality.

Two private lemmas implement the source prerequisites M096.005 and
M096.006, which were absent from the Library base when this proof was
prepared. Their owner is Task 6902
(`92910fb3-bc0c-4de5-a083-ba4d7ddc6261`). Neither adapted public theorem
name is declared here.

- `normValueForSubgroup` is the M096.005 calculation. Choose the finite
  coset quotient's `Fintype`, unfold the defining relative norm sum,
  convert the additive sum of units to a product using `toMul_sum`, and
  move the unit coercion through that product using `map_prod`. Reindex
  by `baseFixingExtensionQuotientEquivGaloisGroup K Ω E` using
  `Fintype.prod_equiv` and the published M096.004 theorem
  `relativeCosetAction_intermediateFieldUnit_val`. Then use
  `Algebra.norm_eq_prod_automorphisms` and the intermediate field's
  structural algebra-map equality.
- `normForSubgroup` is M096.006: apply `Subtype.ext`, `Additive.ext`, and
  `Units.ext`, and finish with `normValueForSubgroup`.

The only adaptation inside these source arguments is replacing
`rw [relativeNormValue]` by `unfold relativeNormValue`. The main membership
argument is unchanged except for unfolding the named proposition and
using the private lemma name.

## Dependencies

The direct imports are the target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.NormSubgroup.Statements`,
the published M096.004 proof module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.U004.Proofs`,
and `Mathlib.RingTheory.Norm.Transitivity`, retained from the source.

The target module supplies the actual ambient-unit representation, fixing
subgroups and their inclusion, fixed-unit equivalences, finite coset
quotient instance, relative norm, finite norm subgroup, and additive
ordinary norm subgroup. These data are reused by their published names.
The proof adds no instance, alternate norm or duplicate public helper.

## Source correspondence and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`:
M096.005 at lines 121–173; M096.006 at lines 177–186;
M096.007 at lines 190–226, with its section parameters at lines 36–37
and 62. The original file SHA-256 is
`b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`.
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public port inventory records no patch10 change for this module;
no applicable NYLL erratum was found in the available errata notes.

Worker 290 extracted these arguments, prefixed the namespace with
`Langlands.NYLL`, replaced broad imports by the focused published modules,
merged the source namespace openings, stated the public theorem through
its exact named proposition, and made the private-lemma and unfolding
adaptations described above. The complete public telescope is unchanged.
The private lemma names and revised explanatory docstrings are local
adaptations, not new mathematical assertions beyond the source.

## Attribution and scope

The original copyright, Apache-2.0 release and author header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply,
with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This support comparison discharges no host class-formation, cup, transfer,
Tate or reciprocity target.
