# Global norm-residue reciprocity as a homeomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian Galois extension `L/K` of number fields, the norm range `N_{L/K}(C_L)` is open in the idele class group `C_K`, so the quotient `C_K / N_{L/K}(C_L)` with its quotient topology is discrete. The Galois group `Gal(L/K)` is finite, hence discrete in the Krull topology. This file uses this to upgrade the algebraic global norm-residue isomorphism, constructed elsewhere in the library, to an isomorphism of topological groups, and records that the norm-residue map on `C_K` is continuous.

## Main definitions and results

All statements assume `[NumberField K] [NumberField L] [FiniteDimensional K L] [IsAbelianGalois K L]`, except the quotient map `ideleClassNormQuotientContinuousMonoidHom`, whose definition uses neither `[FiniteDimensional K L]` nor `[IsAbelianGalois K L]`.

- `ideleClassNormQuotient_discreteTopology`: the quotient `C_K / range (ideleClassNorm K L)` is discrete.
- `globalNormResidueContinuousMulEquiv`: the norm-residue isomorphism `C_K / N_{L/K}(C_L) ≃ₜ* Gal(L/K)`; its value on a class is that of the algebraic `globalNormResidueEquiv`, read multiplicatively.
- `globalReciprocityContinuousMulEquiv`: its inverse `Gal(L/K) ≃ₜ* C_K / N_{L/K}(C_L)`.
- `ideleClassNormQuotientContinuousMonoidHom`: the quotient map `C_K → C_K / N_{L/K}(C_L)` as a continuous homomorphism.
- `globalNormResidueContinuousMonoidHom`: the composite `C_K → Gal(L/K)`, equal pointwise to `globalNormResidueMonoidHom`.
- `globalNormResidueMonoidHom_continuous`: `globalNormResidueMonoidHom K L` is continuous.

## Proofs

Discreteness of the quotient comes from the openness of the norm range, `ideleClassNorm_range_isOpen_universe`, proved in another file. Both directions of the equivalence are then continuous because their domains are discrete.

## Remarks

- The algebraic isomorphism `globalNormResidueEquiv` is stated additively, as an `AddEquiv` between `Additive` types; the maps here convert it with `Additive.ofMul` and `Additive.toMul`.
- The commutative group structure on the idele class group used here comes from local instances (`globalNormResidueIdeleClassCommGroup`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/TopologicalGlobalNormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `feae56f6d5512a81f2a260a7674e4e2eebd32af5069170c9c5798ba2e62a5e5e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
