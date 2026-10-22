# Relative integer and residue maps for supplied realizations

Author: Worker 90. This is one definition and construction unit in
`Langlands.PadicField.TopologicalData`.

For every prime `p`, `F : PadicField.{u} p`, and `E : PadicField.{v} p`, with
independent carrier universes, the input is an actual
`Algebra F.Carrier E.Carrier` compatible with the specified p-adic base through
`IsScalarTower (Padic p) F.Carrier E.Carrier`. The realizations
`T : F.TopologicalData` and `S : E.TopologicalData` are arbitrary supplied data.
The construction uses exactly the published types `T.Integers`, `S.Integers`,
`T.ResidueField`, and `S.ResidueField`.

`relativeIntegerMap T S` restricts `algebraMap F.Carrier E.Carrier` to those
integer rings. Its representative formula is `relativeIntegerMap_coe`.
`relative_mem_integers_iff` proves both preservation and reflection of integer
membership. The proof applies the published
`canonicalNorm_le_one_iff_mem_integers` to each supplied realization, then
`Langlands.Weil.Local.canonicalNorm_map` to the actual base algebra homomorphism
`IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier`. Thus neither valuation
preservation nor integer membership preservation is an extra hypothesis.

`relativeIntegerMap_isLocalHom` proves that the restriction is a local
homomorphism. Given an inverse of the image of an integer, its representative
in the extension field is the image of the original field inverse. Membership
reflection places that inverse in `T.Integers`. Injectivity of the field
embedding verifies the inverse equation in the source integer ring.
This argument uses the actual fields and does not compare the numeric values
of their separately normalized discrete valuations.

`relativeResidueMap T S` is Mathlib's `IsLocalRing.ResidueField.map` applied to
this local homomorphism. Its representative formula is
`relativeResidueMap_residue`: reducing an integer and then applying the residue
map equals applying the integer map and reducing in the target.

The scalar structures are explicit named values, installed locally by callers:

- `relativeIntegerAlgebra T S` is induced by `relativeIntegerMap T S`.
- `relativeResidueAlgebra T S` is induced by `relativeResidueMap T S`.
- `relativeIntegerFieldAlgebra (E := E) T` lets the source integers act on the
  extension field through their inclusion in `F.Carrier` and its given algebra
  map to `E.Carrier`.

The two `relativeIntegerAlgebra_algebraMap` and
`relativeResidueAlgebra_algebraMap` lemmas identify the selected algebra maps
with the constructed ring homomorphisms. No global algebra instance is added.
The single new global instance is the proved localness of the specific
integer ring homomorphism.

The following explicit scalar-tower certificates record compatibility:

| Certificate | Tower, with the scalar choices displayed in its Lean type |
| --- | --- |
| `relativeIntegerFieldTower` | `T.Integers → F.Carrier → E.Carrier` |
| `relativeIntegerTower` | `T.Integers → S.Integers → E.Carrier` |
| `relativeBaseIntegerTower` | the valuation integer ring of `Padic p → T.Integers → S.Integers` |
| `relativeResidueTower` | `T.Integers → T.ResidueField → S.ResidueField` |
| `relativeBaseResidueTower` | `ZMod p → T.ResidueField → S.ResidueField` |

Here the base integer structures are precisely the published `T.integerAlgebra`
and `S.integerAlgebra`. `relativeIntegerMap_baseIntegerMap` proves equality of
the composite with `T.baseIntegerMap` and `S.baseIntegerMap`, using the original
field scalar tower. The residue base structures are precisely `T.residueAlgebra`
and `S.residueAlgebra`. `relativeResidueMap_residueScalarMap` follows from
uniqueness of a ring homomorphism out of `ZMod p`, and supplies the prime-field
tower. `relativeResidueTower` uses the usual quotient algebra structures of the
integer rings on their residue fields; the two paths agree on every integer.

The maps respect identity extensions (`relativeIntegerMap_id` and
`relativeResidueMap_id`). For a third field `D : PadicField.{w} p` and supplied
realization `U`, the composition laws `relativeIntegerMap_comp` and
`relativeResidueMap_comp` use compatible actual field algebra maps.
The universe `w` is independent of `u` and `v`.
`relativeIntegerAlgebraTower` and `relativeResidueAlgebraTower` install all three
explicit relative scalar structures and certify their compatibility.
The integer laws reduce to the field scalar-tower equation; the residue laws
are checked on quotient representatives using surjectivity of reduction.

`relativeIntegerMap_canonical` and `relativeResidueMap_canonical` prove equality
with the published `Langlands.Weil.Local.extensionIntegerMap` and
`extensionResidueMap` for the actual base algebra homomorphism.
The variants ending in `_canonical_of_algHom` take any specified base algebra
homomorphism `f`, explicitly select `f.toRingHom.toAlgebra`, and prove equality
with the existing canonical maps of `f`. These are equalities on the existing
canonical integer rings and residue fields; no replacement objects or
comparison isomorphisms are introduced.

The mathematical provenance is the extension of valuations in Serre,
*Local Fields*, English translation by Marvin Jay Greenberg, GTM 67 (1979),
Chapter II, section 2, Proposition 3 and Corollaries 2–3, printed pages 28–29,
PDF pages 36–37. Worker 90 read the original PDF pages 36–38, including the
normalization discussion on printed page 30, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Registered source: `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
This pair is a derived specialization and explicit functorial construction
from the uniqueness and integer-ring mechanisms in that source. Its proof
route reuses the already published canonical norm and supplied-normalization
comparison, rather than reimplementing Serre's general theorem.

The project imports are `Langlands.LocalField.Normalization.Proof` and
`Langlands.Weil.Local.ExtensionResidue`; both retain their original authorship.
All new definitions and intrinsic compatibility proofs in this pair are
Worker 90's work. The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This unit assumes no Galoisness, equality of ramification indices,
norm-surjectivity, or local class field theory. Relative integral closure,
finite/free modules, relative ramification-degree formulas, and norm/trace
reduction remain subsequent arithmetic work. They are neither conclusions
nor input certificates of these constructions.
