# Frobenius over a larger finite field

Module `Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let k ⊆ E be finite fields and Ω an algebraic extension of E that is also an algebra over k, compatibly (a scalar tower k → E → Ω).

`FiniteField.frobeniusAlgEquivOfAlgebraic E Ω` is Mathlib's arithmetic Frobenius `x ↦ x^|E|` of Ω over E. The theorem `FiniteField.frobeniusAlgEquiv_restrictScalars` says that this Frobenius, viewed as a k-algebra automorphism of Ω, is the power `[E : k]` of the Frobenius of Ω over k.

The proof compares both sides on elements, using `|E| = |k|^[E : k]` and the formula for iterates of Frobenius.

The statement assumes Ω algebraic over both k and E, as Mathlib's `frobeniusAlgEquivOfAlgebraic` requires.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/FieldTheory/FiniteFrobeniusTower.lean`: the Lean file is the source byte for byte (SHA-256 `d5be447d304e80021b15f1808d1a07d85c8a3ab6da6ea17fe50850aeeb0746b5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
