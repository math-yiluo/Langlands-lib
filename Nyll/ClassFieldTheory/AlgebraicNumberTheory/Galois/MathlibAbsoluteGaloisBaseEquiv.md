# Absolute Galois groups along an isomorphism of fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A ring isomorphism e : K ≃ M extends to an isomorphism of algebraic closures; conjugation by it identifies the absolute Galois groups, with their Krull topologies, and their topological abelianizations.

- `semilinearGaloisConjugate e E hE σ`: for field isomorphisms e : K ≃ M and E : Ω ≃ Ψ compatible with the algebra maps (`hE`), the automorphism E ∘ σ ∘ E⁻¹ of Ψ over M.
- `semilinearGaloisEquiv`, `semilinearGaloisContinuousEquiv`: Gal(Ω/K) ≅ Gal(Ψ/M) as groups and as topological groups.
- `semilinearGaloisAbelianizationEquiv_independent`: on topological abelianizations, the induced map does not depend on E; two choices differ by an inner automorphism.
- `absoluteGaloisGroupEquivOfRingEquiv e`: Mathlib's absolute Galois groups of K and M are isomorphic as topological groups, via E = `IsAlgClosure.equivOfEquiv`.
- `absoluteGaloisGroupAbelianizationEquivOfRingEquiv e`: the induced isomorphism of abelianizations.

The isomorphism of absolute Galois groups depends on the chosen extension of e; only its abelianization is shown independent of it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/MathlibAbsoluteGaloisBaseEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `464ddae84fe4860aaa3efa2db1528c2d5fd2dce9da08588b26b39af15fc81711`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
