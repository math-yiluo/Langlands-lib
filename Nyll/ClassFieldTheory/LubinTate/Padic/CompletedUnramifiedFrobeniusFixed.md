# Fixed points of the Frobenius on the completed unramified field

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let W = W(F̄_p) be the Witt vectors over an algebraic closure of 𝔽_p, and let its fraction field be the completed unramified coefficient field of the library's p-adic Lubin–Tate theory. This file shows that the Frobenius fixes exactly ℤ_p in W and exactly ℚ_p in the fraction field.

## Main results

- `padicCompletedUnramifiedWittRing_frobenius_fixed_iff`: a Witt vector `x` in W satisfies `WittVector.frobenius x = x` if and only if `x` is the image of some `z : ℤ_[p]` under the canonical map `padicIntToCompletedUnramifiedWittRing p`.
- `padicCompletedUnramifiedFrobenius_fixed_iff`: an element `x` of the fraction field is fixed by the arithmetic Frobenius `padicCompletedUnramifiedFrobenius p` if and only if it is the image of some `q : ℚ_[p]` under the algebra map.

## Proofs

For the Witt ring: the Frobenius acts on coordinates by the p-th power, so a fixed vector has every coordinate fixed by x ↦ xᵖ, hence in the prime field 𝔽_p; the vector then comes from W(𝔽_p), which Mathlib identifies with ℤ_p. For the field: write `x = a / b` and the denominator `b` as pᵐ times a unit. Then pᵐ·x lies in W, is fixed because pᵐ is fixed (it comes from ℚ_p), so it comes from ℤ_p, and `x` is its image divided by pᵐ. The converse directions hold because the Frobenius is a ℚ_p-algebra map fixing ℤ_p.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedUnramifiedFrobeniusFixed.lean`: the Lean file is the source byte for byte (SHA-256 `416933092789b9a5f01293a23bdd95345d1ef6a3da4856bbdacd6b76f6840339`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
