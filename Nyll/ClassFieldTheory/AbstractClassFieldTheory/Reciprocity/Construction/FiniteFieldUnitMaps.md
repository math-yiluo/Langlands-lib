# Unit groups of abstract finite fields: actions, inclusions and norms

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of a group `G` with a `G`-module `A` (a `Rep ℤ G`), a degree map `D` and valuation data `v`, the unit group of an abstract field is the subgroup `v.unitAddSubgroup` of the `A`-invariants of normalized valuation zero. This file shows that the maps needed in the reciprocity construction preserve units: the action on a Frobenius fixed field of a quotient element commuting with the Frobenius element, the inclusion along a finite extension, and the relative norm.

## Main definitions and results

- Two instances carry normality of an extension subgroup and finiteness of its index over to the residue-field enrichment `toFiniteResidueAbstractField D` of a finite abstract field; the enrichment does not change the underlying field.
- `valuationAt_frobeniusFixedFieldAction`: for `G` compact, Hausdorff and totally disconnected, a finite residue abstract field `K`, a closed subgroup `L ≤ K` normal in `K`, a Frobenius element `σ` and a class `q` of `K` modulo the inertia subgroup that commutes with `σ`, the action of `q` on the invariants of the Frobenius fixed field (with that field of finite index in the base field) preserves the normalized valuation.
- `frobeniusFixedFieldUnitAction`: under the same hypotheses, this action restricted to an additive endomorphism of the unit group of the Frobenius fixed field.
- `fixedFieldInclusion_mem_unitAddSubgroup` and `finiteUnitInclusion`: for a finite abstract field extension `E`, inclusion of invariants sends units of `E.base` to units of `E.field`, giving a homomorphism of unit groups.
- `relativeNorm_mem_unitAddSubgroup` and `finiteUnitNorm`: the relative norm from `E.field` to `E.base` sends units to units, giving a homomorphism of unit groups.
- `finiteUnitInclusion_transport_coe`: transporting a unit inclusion along an equality of target fields does not change the underlying element of `A`.

## Proofs

The valuation invariance uses that `q` conjugates the Frobenius fixed field to itself (proved in an earlier file of the construction) and that the normalized valuation is compatible with conjugation. Both unit statements come from the tower formula for the normalized valuation: the residue degree times the valuation upstairs equals the valuation of the norm downstairs. For the inclusion one uses that the norm of an included element is its multiple by the degree, and cancels the residue degree, as multiplication by a nonzero natural number on the profinite integers is injective.

## Watch for

The unit groups and all maps are additive: the module `A` is written additively, so the multiplicative unit group of a field appears as an `AddSubgroup`, and norms and inclusions are `→+` homomorphisms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`: the Lean file is the source byte for byte (SHA-256 `69b451e32ff394f20c87f0e67e26f24a4f2b3e3906cf5ed8665d0eac8a45e536`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
