# NYLL M225.009 and M228.002: residue units and the first principal-unit quotient

This module constructs the canonical residue homomorphism on valuation-ring
units and its induced multiplicative equivalence
`O_Kˣ / U_K¹ ≃* k_Kˣ`. It uses the published complete discrete valuation field
package, its actual residue projection, and the concrete principal-unit subgroup.

## Declarations and parameters

Both declarations are in the namespace
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`.
Both retain independent universes `u v`, implicit `{K : Type u} [Field K]`,
and explicit
`(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)`.
There are no additional hypotheses.

| Declaration | Type and construction |
| --- | --- |
| `residueUnitHom F` | `F.valuationSubringˣ →* F.residueFieldˣ`, defined as `Units.map F.residueMap.toMonoidHom`. |
| `unitsModOneEquivResidueFieldUnits F` | `F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1 ≃* F.residueFieldˣ`, constructed by `QuotientGroup.liftEquiv` from `residueUnitHom F`. |

Here `higherPrincipalUnitGroup` is imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`.
Its carrier at level one is
`{a | (a : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ 1}`.
The residue data come from the published complete-DVF projections imported by
that module. The local-ring structures and normality of the subgroup of the
commutative unit group are provided by the existing canonical instances.

The forward equivalence is the map induced by this particular residue
homomorphism. For every `a : F.valuationSubringˣ`, its representative formula is

```lean
unitsModOneEquivResidueFieldUnits F
    (QuotientGroup.mk' (higherPrincipalUnitGroup F 1) a) =
  residueUnitHom F a
```

This formula holds by `rfl`, as does the formula identifying the underlying
residue of `residueUnitHom F a` with `F.residueMap (a : F.valuationSubring)`.
These are defining properties of the two constructions; this module does not
introduce separate theorem declarations for them.

## Local construction arguments

The kernel equality needed by `QuotientGroup.liftEquiv` is proved inside the
equivalence definition. Subgroup extensionality and the concrete carrier reduce
it to
`Units.map F.residueMap.toMonoidHom a = 1` if and only if
`(a : F.valuationSubring) - 1 ∈ F.maximalIdeal`, using `pow_one`.
In the forward direction, coercing the equality of units gives residue equal
to one. The residue of `a - 1` is then zero by preservation of subtraction
and one, so `IsLocalRing.residue_eq_zero_iff` gives maximal-ideal membership.
Conversely, that lemma turns maximal-ideal membership into residue zero for
`a - 1`; preservation of subtraction gives residue of `a` equal to one,
and `Units.ext` gives equality of units.

Surjectivity is
`IsLocalRing.surjective_units_map_of_local_ringHom` applied to `F.residueMap`,
with `IsLocalRing.residue_surjective` and the canonical `IsLocalHom` instance.
The Mathlib argument lifts a residue unit along the surjective ring map, reflects
its unit property along the local homomorphism, and takes that unit as a
preimage. Thus neither a finite residue field, a chosen uniformizer, nor a
supplied equivalence is needed. `QuotientGroup.liftEquiv` then supplies the
multiplicative equivalence with the stated action on representatives.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`:

- M225.009, `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Filtration.lean:182–184`,
  defines `residueUnitHom`. The file SHA-256 is
  `26c1fdb63f9766b4dd8e6f43e2c7c0d97593a3afb0df2e9d5b8a129d0f5ed4bb`.
- M228.002, `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/ResidueQuotient.lean:48–57`,
  constructs `unitsModOneEquivResidueFieldUnits`. The file SHA-256 is
  `d6a4e2f7befa4540da6216a5fc840a646e043c5e0a352a7fd960d88cbdc387ea`.

These are retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Worker 713 adapted these declarations using Worker 298's unreviewed
`ResidueComparisonProbe.lean`, shared in revision 15 of task
`b40189a0-d43f-4b89-a953-52116f09eaa0`. That probe is an implementation recipe,
not an accepted result.

The changes from the pinned source are:

- Add the `Langlands.NYLL` namespace prefix and isolate the two declarations
  in this paired module, retaining binder order, explicitness and both universes.
- Replace the source import closure, including `AutomorphismTransport`, by the
  published subgroup definition and direct Mathlib imports
  `RingTheory.LocalRing.RingHom.Basic`, `Algebra.Group.Units.Hom`, and
  `GroupTheory.QuotientGroup.Basic`. Omit unused opens and `BigOperators` scope.
- Retain the residue homomorphism's defining expression. Retain the
  `QuotientGroup.liftEquiv` construction, but inline its kernel equality as
  described above rather than importing source theorem wrappers
  M225.011/M225.012/M228.001.
- Replace the source surjectivity wrapper `F.residue_surjective` with the
  canonical Mathlib theorem `IsLocalRing.residue_surjective`. The local-map
  instance remains canonical. Shorten names within the declaration namespace
  and use `simpa only` for the residue-unit homomorphism.
- Place both declarations in a `noncomputable section`, omitting the redundant
  declaration-level `noncomputable` on the equivalence. Add the module comment
  and reflow the residue-map docstring.

The local kernel proof is construction support derived from the published
subgroup carrier and Mathlib residue facts. No additional public construction
or auxiliary theorem family is introduced. The original copyright, author
and Apache-2.0 notices are retained in the Lean header, with the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
