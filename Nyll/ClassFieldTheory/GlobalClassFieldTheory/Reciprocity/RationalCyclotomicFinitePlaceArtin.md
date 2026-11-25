# Finite-place Artin symbols in rational cyclotomic fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For `m : ℕ+` let `ℚ(ζ_m)` be `KummerTheory.rationalCyclotomicLevel m`. The file computes the cyclotomic character `IsCyclotomicExtension.Rat.galEquivZMod : Gal(ℚ(ζ_m) / ℚ) ≃ (ZMod m)ˣ` of the library's chosen finite-place Artin symbol at a rational prime `q`: for `q ∤ m` it is `q` raised to the normalised local valuation; for `m = p ^ (n + 1)`, at `q = p` and on a rational principal idele, it is the reduction of the `p`-adic unit part.

## Main definitions and results

- `rationalFinitePlaceCompletionRingEquivPadic q` and `rationalFinitePlaceCompletionIntegerRingEquivPadicInt q`: the completion of `ℚ` at `q` is identified with `ℚ_[q]`, its valuation ring with `ℤ_[q]`, compatibly with `ℚ` and with the valuations. Named local-field structures on this completion (`rationalPrimeFactorCompletion...`) are exposed for other files.
- `rationalPrincipalFiniteComponent_valuationMap`: for `x : ℚˣ`, the normalised valuation (`valuationMap`) of the `q`-component of the principal idele of `x` is `−v_q(x)`; the prime `q` itself has value `−1`.
- `galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd`: for `q ∤ m` and `x ∈ ℚ_qˣ`, the character of the chosen Artin symbol is `(q mod m) ^ valuationMap(x)`. If this exponent (`rationalCyclotomicArtinLocalExponent`) is `0`, the character and the Artin symbol itself are trivial (`..._eq_one_of_not_dvd_of_localExponent_eq_zero`). For principal `x` the value is `q ^ (−v_q(x))` (`..._principal_of_not_dvd`).
- `padicMultiplicativeLevel_isCyclotomicExtension`: level `n` of the standard multiplicative Lubin–Tate tower over `ℚ_[p]` is the `p ^ (n + 1)`-cyclotomic extension. `rationalCyclotomicLocalizedCompletionPadicAlgEquiv` identifies the localisation of `ℚ(ζ_m)` at `p`, for that prime power `m`, with it over `ℚ_[p]`.
- `finitePlaceArtinMonoidHomOfExtension_eq_one_of_semilinear` (fields in `Type`): if the local Artin value is trivial in an extension identified semilinearly and valuation-compatibly with the completed one, the finite-place Artin value is trivial; `rationalCyclotomicPrincipalPrime_finitePlaceArtinOfExtension_eq_one_of_padic` specialises it to the Lubin–Tate level.
- `galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime`: the character of `rationalCyclotomicPrincipalPrimeChosenArtin p n x`, the Artin symbol at `p` of a principal `x : ℚˣ`, is the reduction modulo `p ^ (n + 1)` of the unit `p ^ (−v_p(x)) · x` of `ℤ_[p]`.

## Proofs

Away from `m`, the completed extension is unramified, so the local Artin map is arithmetic Frobenius to the power `valuationMap` (`abelianLocalArtinMonoidHom_eq_frobenius_zpow`); Frobenius raises the primitive root to the `q`-th power since the residue field has `q` elements, and the decomposition group carries this to the global field. At `p`, semilinear naturality of the local Artin map moves the computation to the Lubin–Tate level, where the unit part acts on the primitive root by the corresponding power.

## Remarks

- The local reciprocity normalisation is the library's "inverse-standard" one: a prime element has normalised value `−1`, hence the exponent `−v_q(x)`.
- The ramified computation covers only prime-power levels `p ^ (n + 1)` and principal ideles of `ℚ`, and is stated for the named definition `rationalCyclotomicPrincipalPrimeChosenArtin`, the local-to-global factored form at `rationalCyclotomicChosenFinitePlaceExtension`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicFinitePlaceArtin.lean`: the Lean file is the source byte for byte (SHA-256 `8f3a964a3f8faa1fe7e0529a21c862b8bb95ad1601089f100ad8410f8ed6d0ee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
