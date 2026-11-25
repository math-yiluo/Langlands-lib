# Global reciprocity for finite Galois extensions as a homeomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidueAbelianization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, global norm-residue reciprocity identifies `C_K / N_{L/K}(C_L)` with the abelianization `Gal(L/K)ᵃᵇ`. This file upgrades the algebraic isomorphism, constructed elsewhere in the library, to an isomorphism of topological groups in both directions, and records that the norm-residue map `C_K → Gal(L/K)ᵃᵇ` is continuous. It is the non-abelian counterpart of the file treating finite abelian extensions.

## Main definitions and results

The statements below assume `[NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]`, except `finiteGaloisAbelianization_discreteTopology`, which omits the number-field and Galois instances.

- `ideleClassNormAbelianizationQuotient_discreteTopology`: the quotient of `C_K` by the range of `ideleClassNorm K L` is discrete.
- `finiteGaloisAbelianization_discreteTopology`: `Abelianization (Gal(L/K))`, with the quotient topology of the Krull topology, is discrete (finiteness of `L/K` suffices).
- `globalNormResidueAbelianizationContinuousMulEquiv`: `C_K / N_{L/K}(C_L) ≃ₜ* Gal(L/K)ᵃᵇ`, evaluating to the algebraic `globalNormResidueAbelianizationEquiv`.
- `globalReciprocityAbelianizationContinuousMulEquiv`: its inverse.
- `globalNormResidueAbelianizationContinuousMonoidHom`: the quotient map followed by the equivalence, a continuous homomorphism `C_K → Gal(L/K)ᵃᵇ` equal pointwise to `globalNormResidueAbelianizationMonoidHom`; the latter is continuous (`globalNormResidueAbelianizationMonoidHom_continuous`).

## Proofs

The norm quotient is discrete because the norm range is open, `ideleClassNorm_range_isOpen_universe`, proved in another file. The abelianization is discrete as a quotient of a finite discrete group. Continuity of both directions follows from discreteness.

## Remarks

- Mathlib's `Abelianization` carries no topology; the file installs the quotient topology from `Gal(L/K) ⧸ commutator` as a local instance. The commutativity of the idele class group and both discreteness facts are also local instances.
- The algebraic isomorphism is an `AddEquiv` between `Additive` types and is converted with `Additive.ofMul`/`Additive.toMul`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/TopologicalGlobalNormResidueAbelianization.lean`: the Lean file is the source byte for byte (SHA-256 `3b3ca7a86c555482355f969bd3be4fefea31fae30f6b6be4c6095ded52ed4156`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
