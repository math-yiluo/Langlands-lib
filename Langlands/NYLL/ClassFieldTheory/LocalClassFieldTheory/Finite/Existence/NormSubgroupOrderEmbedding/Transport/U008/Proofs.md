# NYLL M300.008: transport of the actual finite abelian norm subgroup

The theorem
`Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup`
proves the published target
`Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianNormSubgroup_eq_additiveNormSubgroupStatement K L`.
Its complete telescope is `(K : Type) [Field K]` followed by explicit
`(L : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K))`.
The field is in universe zero, as in the original source.

## Source and attribution

The proof is adapted from Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
M300.008, lines 236–301 (type 236–241; proof 242–301).
The original file's SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The Apache-2.0 copyright and author header is preserved. The original license
and notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 538 performed this focused proof adaptation.

## Exact mathematical content

For the actual intermediate field
`E := abstractFixedField K (SeparableClosure K) L.field`, the theorem identifies
these additive subgroups of `Additive Kˣ`:

```lean
(L.normSubgroup (intrinsicAbsoluteUnits K)).map
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
  additiveNormSubgroup K E
```

The left side maps the abstract relative-norm image through the inverse of the
canonical base-unit equivalence. The right side is the additive form of the
ordinary field norm's image on units. Both are the published actual norm
subgroups; no arbitrary supplied subgroup or norm equality replaces them.
The target has no local-field, valuation, topology, finite-dimensionality or
Galois hypothesis beyond the given finite abelian subextension. The additional
instances needed by the proof are constructed locally from that subextension.

## Implemented proof

1. Install quotient finiteness over the intrinsic base using `L.finite`.
   M300.001 supplies quotient finiteness over `baseField`.
2. Set `E` to the represented fixed field. M099.005 supplies
   `FiniteDimensional K E`, and M299.005 applied to M300.002 supplies
   `IsGalois K E`.
3. Use additive subgroup extensionality. For the forward inclusion, unpack a
   mapped abstract norm witness `b`. The inverse fixed-field unit equivalence
   gives a unit `u : Eˣ` representing `b`. M300.007 rewrites its transported
   relative norm as `Additive.ofMul (normUnits K E u)`, which lies in the
   native norm subgroup with witness `u`.
4. For the reverse inclusion, unpack a native norm witness `u : Eˣ`.
   Use `baseUnitsEquivGaloisAmbientFixed (Additive.ofMul (normUnits K E u))`
   as the mapped element. Its membership in the abstract norm image is
   witnessed by the fixed-field unit equivalence applied to `u`.
   Injectivity of the inverse base-unit equivalence and M300.007 prove the
   witness equality; the inverse equivalence law and the original native norm
   equality prove the required image equality.

The abstract norm subgroup reduces to the range of `relativeNorm`, and the
native norm subgroup reduces to the range of `normUnits`. The proof therefore
uses the definitions of the published constructions directly when unpacking
and constructing range witnesses. M300.007 is consumed as a separate theorem;
none of its field-value norm prerequisites is reproved here.

## Reused proof interfaces

All declarations below are under `Langlands.NYLL.LocalClassFieldTheory`.

| Source unit | Declaration | Role |
| --- | --- | --- |
| M300.001 | `finiteAbelianSubextension_finite_over_absoluteBase` | Finite quotient over the abstract absolute base |
| M300.002 | `finiteAbelianSubextension_normal_over_absoluteBase` | Normal extension subgroup over that base |
| M099.005 | `abstractFixedField_finiteDimensional` | Finite-dimensionality of the actual fixed field |
| M299.005 | `abstractFixedField_isGalois_of_base_normal` | Galois structure on the actual fixed field |
| M300.007 | `baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits` | Identification of the two norm values |

The imports also supply the target statement, actual relative norm, both
unit equivalences, and the native norm constructions. All imports use the
`Langlands.NYLL` Library modules.

## Modification record

1. Extract only source M300.008, including the full proof, and preserve its
   inherited noncomputable section and complete `K`/field/`L` telescope.
2. Prefix the namespace with `Langlands.NYLL`. State the theorem as the
   published `Statement K L`, followed by a definitional `change` to the source
   subgroup equality. The proof after this `change` is the source proof.
3. Replace the broad upstream imports by focused Library imports for the
   target, M300.001/.002, M099.005, M299.005 and M300.007.
4. Retain `open LocalFieldTheory CyclicCohomology ClassFormation`; omit the
   unused source openings of `RamificationTheory` and `KummerTheory`.
5. Replace the module description with a focused description of this proof
   and its adaptation. Preserve the theorem's source docstring and the original
   copyright and author header.

No theorem hypothesis, universe, fixed field, norm map, subgroup, equivalence
orientation or conclusion is changed.
