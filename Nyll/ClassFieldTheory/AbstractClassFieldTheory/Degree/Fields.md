# Degree data, abstract fields and the fundamental identity

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file opens abstract valuation theory for class formations. The datum is a group `G` with a topology and a continuous surjective degree homomorphism `d : G → ℤ̂`. An abstract field is a closed subgroup of `G`, read contravariantly (a smaller subgroup is a larger field), and the file attaches degrees, residue degrees and ramification indices to inclusions of such subgroups.

## Main definitions

- `ZHatMul`: `ℤ̂` written multiplicatively. `DegreeData G` bundles `degree : G → ZHatMul`, continuous and surjective.
- `baseField G`: the base field, represented by all of `G`. `DegreeData.inertia` is `ker d`; `fieldInertia K = K ∩ ker d`; `fieldImage K = d(K)`; `residueDegreeCardinal K` is the cardinality of `ℤ̂ / d(K)` (`residueQuotient`).
- `AbstractExtension G`: closed subgroups `field ≤ base`. Its `degreeCardinal`, `relativeResidueDegreeCardinal` and `relativeRamificationIndexCardinal` are the cardinalities of the coset spaces `base / field`, `d(base) / d(field)` and `(base ∩ ker d) / (field ∩ ker d)`.
- `IsUnramified`: `base ∩ ker d ≤ field`. `IsTotallyRamified`: `d(base) ≤ d(field)`.
- `GaloisSubextension K`: a closed `L ≤ K` normal in `K`, with quotient group `extensionQuotient`; no finiteness.
- Bundles carrying finiteness of the relevant quotients: `FiniteAbstractExtension`, `FiniteResidueAbstractExtension` and `FiniteAbstractFieldExtension` (extensions, with `ℕ+`-valued `degree`, `residueDegree` and `ramificationIndex`); `FiniteResidueAbstractField` and `FiniteAbstractField` (finite over `baseField G`), with an absolute `residueDegree`; `FiniteTower`, two adjacent finite extensions.

## Main results

- `degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal`: for every extension, without finiteness, `[base : field] = f · e` as cardinals.
- `relativeResidueDegreeCardinal_mul_residueDegreeCardinal`: the relative residue cardinal times that of the base is that of the field.
- `Tower.degreeCardinal_mul`, `Tower.relativeResidueDegreeCardinal_mul`, `Tower.relativeRamificationIndexCardinal_mul`: multiplicativity in towers.
- Unramified gives `e = 1`, totally ramified gives `f = 1`, with the resulting degree equalities, in both the cardinal and the finite setting.
- `FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex`: `n = f · e` in `ℕ`; also `isTotallyRamified_iff_residueDegree_eq_one`.
- Finiteness transfer: over a field with finite residue quotient, a field with finite relative residue quotient again has one (`FiniteResidueAbstractField.ofRelativeInclusion`), in particular a finite extension (`FiniteResidueAbstractExtension.ofInclusion`); a field finite over the base has finite residue quotient (`FiniteAbstractField.toFiniteResidueAbstractField`); a finite extension of a field finite over the base is finite over the base (`FiniteAbstractFieldExtension.ofInclusion`). The base field has residue degree one (`base_residueDegree`).

## Points to watch

- Degrees are cardinals in general and positive naturals only on the finite bundles; an infinite index is never encoded as `0`, unlike Mathlib's `Subgroup.index`.
- In the cardinal fundamental identity the residue cardinal is lifted from universe 0, where `ℤ̂` lives, to the universe `u` of `G`.
- Unramified and totally ramified are the library's own containment conditions, not conditions on indices.
- `DegreeData` does not ask `G` to be profinite; results needing it must assume it separately.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`: the Lean file is the source byte for byte (SHA-256 `d28800ee78d6ebf363c2b2b8e0c4a9d33eebcb275d61d113f4fa36ec13651218`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
