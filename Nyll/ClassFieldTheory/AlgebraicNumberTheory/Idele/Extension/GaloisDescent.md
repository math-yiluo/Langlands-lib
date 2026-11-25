# Galois descent for idele classes: C_L^G = C_K

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, with `C_L` modelled as the relative idele class group `ClassGroup K L` (units of `𝔸_K ⊗_K L` modulo `Lˣ`), the file proves that the classes fixed by `Gal(L/K)` are exactly the image of `C_K`.

## Main declarations

- `principalIdele_injective`: `Lˣ` embeds in the relative ideles.
- `principalQuotientAction` (instance): the Galois action preserves the principal subgroup and so acts on `ClassGroup K L`; `smul_class_mk` computes it on representatives, and `relativeIdeleClassMulDistribMulAction` is the same action by group automorphisms (a reducible def).
- `galoisFixedClassSubgroup`: the subgroup of classes fixed by every `σ`.
- `classInclusion_range_le_galoisFixed`: classes coming from `C_K` are fixed.
- `exists_fixed_representative_of_fixed_class`: a fixed class has a representative idele fixed by every `σ`.
- `galoisFixed_le_classInclusion_range` and `classInclusion_range_eq_galoisFixedClassSubgroup`: every fixed class comes from `C_K`, so the image of `classInclusion` equals the fixed subgroup.

## Proof

For a fixed class of `a`, the quotients `σ(a)/a` are principal, `= x_σ`; the `x_σ` form a 1-cocycle `Gal(L/K) → Lˣ`, which is a coboundary by Hilbert 90 in Noether's form (`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`), say `x_σ = σ(β)/β`. Then `a/β` is a fixed representative, and fixed relative ideles come from `I_K` by `inclusion_range_eq_galoisFixedSubgroup`.

## Points to watch

- The statement concerns the library's tensor-product model of `C_L`, not a quotient of Mathlib's ideles of `L`.
- The descent results need `IsGalois K L`; the number-field hypothesis on `L` is dropped.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/GaloisDescent.lean`: the Lean file is the source byte for byte (SHA-256 `52808e837356d124f5251fccb5bf30330cdba41867fb9e5fd58cb32a6b25d7cf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
