# Finite inertia fixed field and comparison maps

Worker 104 implemented this derived definition adapter. Worker 384 contributed
the interface design and identified the existing actions on supplied integer
rings and residue fields. Imported Library and Mathlib constructions retain
their original authorship.

All declarations in this pair belong to `Langlands.LocalClassField.NYLL`.
The inputs are any prime `p`, `F : PadicField.{u} p`, and
`E : PadicField.{v} p`, with independent universes `u` and `v`, an actual
`Algebra F.Carrier E.Carrier`, its compatible
`IsScalarTower (Padic p) F.Carrier E.Carrier`, and arbitrary
`TF : F.TopologicalData`. Finite-dimensionality of `E.Carrier` over
`F.Carrier` follows from the supplied finite-dimensional p-adic structures by
`FiniteDimensional.right`. The construction does not restrict either carrier
to `Type 0` or exclude any prime.

## The fixed intermediate field

`finiteInertiaSubgroup F E TF` installs `TF.topology`, `TF.valuativeRel`, and
`TF.localField`, then uses `LocalGalois.localNormedField F.Carrier` with its
proved ultrametric and completeness instances. In precisely this setup it is
`LocalGalois.inertia F.Carrier E.Carrier`, the kernel of the existing
`LocalGalois.residueHom`. No arbitrary subgroup or residue-action certificate
is an input.

The residue rings in that kernel are the actual quotients of
`LocalGalois.baseIntegers F.Carrier` and
`LocalGalois.extensionIntegers F.Carrier E.Carrier`. The first integer ring
comes from the valuation of the norm just constructed on `F.Carrier`; the
second comes from `LocalGalois.spectralValuation F.Carrier E.Carrier`.
The residue action is an algebra automorphism over the first residue field,
obtained by restricting each field automorphism to the second integer ring
and passing to its quotient. In particular, this definition does not use an
independently supplied `TE : E.TopologicalData`.

`finiteInertiaField F E TF` is exactly
`IntermediateField.fixedField (finiteInertiaSubgroup F E TF)` in the given
extension. Write `U` for this intermediate field: its elements are the
`x : E.Carrier` fixed by every member of that subgroup. This notation is only
an abbreviation in this document. The code exposes the actual intermediate
field and its subtype, rather than a separately chosen isomorphic field.
Neither this definition nor its name asserts unramifiedness.

The definitions of the subgroup and field need no Galois or abelian hypothesis.
The restriction map below is provided when `E.Carrier/F.Carrier` is Galois.

## Field maps and scalar structures

`finiteInertiaEmbedding` is `U.val : U →ₐ[F.Carrier] E.Carrier`.
`finiteInertiaEmbedding_apply` records that its value is the subtype's
underlying element of `E.Carrier`.

`finiteInertiaPadicField` is a reducible package of the same subtype as a
`PadicField.{v} p`. Its field and `F.Carrier` algebra structures are the
intermediate-field ones. The `Padic p` algebra is the inherited
intermediate-field structure through `F.Carrier`, and its finite-dimensional
certificate is `FiniteDimensional.trans (Padic p) F.Carrier U`. The carrier
remains in universe `v`.

`finiteInertiaBaseEmbedding` is the p-adic algebra map from `F.Carrier` to
this package, using `IsScalarTower.toAlgHom`. `finiteInertiaPadicEmbedding`
is `U.val` restricted to `Padic p` scalars. The equation
`finiteInertiaPadicEmbedding_base` says their composite is the given
`algebraMap F.Carrier E.Carrier` on every element.

The explicit certificates are:

| Declaration | Meaning |
| --- | --- |
| `finiteInertiaPadicTower` | The tower `Padic p → U → E.Carrier` uses the inherited scalar maps. |
| `finiteInertiaBaseTower` | The tower `Padic p → F.Carrier → U` uses those same structures. |
| `finiteInertiaFieldTower` | The tower `F.Carrier → U → E.Carrier` is the actual intermediate-field tower. |
| `finiteInertiaField_finiteDimensional` | `U` is finite-dimensional over `F.Carrier`. |

The first certificate is proved by `IsScalarTower.of_algebraMap_eq` with a
reflexive algebra-map identity. The other three reuse intermediate-field
instances. `finiteInertiaPadicTower` is made an instance only locally in this
file. No new global algebra or scalar-tower instance is installed.

## Maps and actions for arbitrary supplied realizations

Let `TU : (finiteInertiaPadicField F E TF).TopologicalData` and
`TE : E.TopologicalData` be arbitrary. Their integer rings and residue fields
are exactly `TU.Integers`, `TE.Integers`, `TU.ResidueField`, and
`TE.ResidueField`. No canonical realization is imposed on either one.

The following reducible aliases reuse
`PadicField.TopologicalData.relativeIntegerMap` and
`PadicField.TopologicalData.relativeResidueMap` from
`Langlands.LocalField.RelativeIntegers`:

| Alias | Actual source and target |
| --- | --- |
| `finiteInertiaIntegerMap F E TF TU TE` | `TU.Integers →+* TE.Integers` |
| `finiteInertiaResidueMap F E TF TU TE` | `TU.ResidueField →+* TE.ResidueField` |
| `finiteInertiaBaseIntegerMap F E TF TU` | `TF.Integers →+* TU.Integers` |
| `finiteInertiaBaseResidueMap F E TF TU` | `TF.ResidueField →+* TU.ResidueField` |

The integer maps restrict the actual field algebra maps. The residue maps are
induced by those local integer-ring homomorphisms. Their representative laws
are the existing `relativeIntegerMap_coe` and
`relativeResidueMap_residue`. `finiteInertiaIntegerMap_comp` and
`finiteInertiaResidueMap_comp` say that composing the two displayed maps gives
`relativeIntegerMap TF TE` and `relativeResidueMap TF TE`, respectively.
Their proofs are the symmetric forms of the existing relative composition
laws, applied to the actual tower.

Scalar structures for these rings remain the explicit values already provided
by `RelativeIntegers`: `relativeIntegerAlgebra TF TU`,
`relativeIntegerAlgebra TU TE`, `relativeResidueAlgebra TF TU`, and
`relativeResidueAlgebra TU TE`, together with the corresponding values for
`TF TE`. Their algebra maps are the respective relative maps, and
`relativeIntegerAlgebraTower TF TU TE` and
`relativeResidueAlgebraTower TF TU TE` certify compatibility. Callers can install
these named values locally. The aliases introduce no alternative scalar
structures.

`finiteInertiaIntegerAction F E TF TU` reuses
`Ramification.Padic.integerAutHom TU F.Carrier` as a homomorphism
`Gal(U/F.Carrier) →* RingAut TU.Integers`.
`finiteInertiaResidueAction F E TF TU` reuses
`Ramification.Padic.residueHom TU F.Carrier` as a homomorphism
`Gal(U/F.Carrier) →* RingAut TU.ResidueField`.
They are the existing restrictions of actual field automorphisms and the
induced quotient action. Their target is a ring automorphism group; this pair
does not additionally package the residue action as an algebra automorphism
over `TF.ResidueField`. The full extension's supplied-data actions are already
`Ramification.Padic.integerAutHom TE F.Carrier` and
`Ramification.Padic.residueHom TE F.Carrier`.

The spectral integer and residue inclusions also already exist:
`LocalGalois.integerInclusion F.Carrier E.Carrier U` and
`LocalGalois.residueInclusion F.Carrier E.Carrier U`, using the same local norm
setup as in the definition of inertia. Their source rings are the spectral
integer ring of `U` and its residue field. They are not identified here with
`TU.Integers` and `TU.ResidueField`. The existing
`LocalGalois.residueHom_restrict` in
`Langlands.Galois.Local.AbsoluteProof` gives the restriction square for those
spectral maps. A consumer of that theorem must import that proof module;
this definition unit imports `AbsoluteDefinitions`.

## Galois structure and restriction

Under `IsGalois F.Carrier E.Carrier`,
`finiteInertiaField_isGalois` proves `IsGalois F.Carrier U`. Its proof reinstalls
the same local norm setup, uses the normality of the kernel
`LocalGalois.inertia`, and applies
`IsGalois.of_fixedField_normal_subgroup`.

`finiteInertiaRestriction F E TF` is the group homomorphism
`Gal(E.Carrier/F.Carrier) →* Gal(U/F.Carrier)` constructed by
`AlgEquiv.restrictNormalHom U`. The lemma
`finiteInertiaRestriction_apply` says that including the value of a restricted
automorphism in `E.Carrier` equals applying the original automorphism to the
included element. Its proof is `AlgEquiv.restrictNormal_commutes`.
The Galois certificate is installed only locally for this construction.

Under `IsAbelianGalois F.Carrier E.Carrier`,
`finiteInertiaField_isAbelianGalois` reuses Mathlib's intermediate-field
instance to prove the corresponding assertion for the packaged field `U`.
It does not need an additional separately supplied Galois certificate.

## Provenance and remaining arithmetic

This pair is a derived adapter of published Library and Mathlib objects,
not a port of an external NYLL theorem. Searches for a finite fixed-field
adapter found the generic `IntermediateField.fixedField`, the actual
`LocalGalois.inertia`, and existing absolute fixed-field constructions; this
pair specializes and packages those existing notions. It reuses the supplied
maps authored in `RelativeIntegers` and the actual actions in
`Langlands.LocalFactor.Ramification.Galois`. No NYLL source closure is imported.

The source context is Serre, *Local Fields* (1979), Chapter II, section 2,
Proposition 3 and Corollaries 1–4, printed pages 28–30 (PDF pages 36–38),
on extension valuations and conjugacy invariance. The intended later
unramified-subextension interpretation is motivated by Chapter III, section 5,
Theorems 1–3 and their corollaries, printed pages 53–55 (PDF pages 60–62).
Worker 104 read those original PDF pages. Registered source:
`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The present elementary proofs follow the existing Lean APIs described above;
this pair does not prove Serre's unramified-extension theorems.

Subsequent units must identify the spectral valuation, integer rings, residue
fields and actions with the arbitrary supplied realizations, and prove the
needed independence of choices. In particular, this pair does not prove the
supplied-data residue-action restriction square, ramification index
`e(U/F) = 1`, or surjectivity of the residue map from `U` to `E`. It also does
not prove residue-action bijectivity for `U/F` or a comparison with the host's
inverse-action geometric congruence. The existing canonical maps and
canonical-comparison results in `RelativeIntegers` remain available; choosing
canonical data alone does not establish these further spectral and action
comparisons. No such property is inserted as an input certificate here.

There is no reciprocity map, reciprocity theorem, class-formation certificate,
or comparison with the cohomological route in this unit. Its environment is
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
