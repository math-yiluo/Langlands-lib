# Restricting valuation rings to finite separable subextensions

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects the lemmas that reduce questions about a valuation ring of an algebraic extension `Ω / K` (for instance an algebraic closure) to finite separable subextensions. Every element of `Ω` has a positive power in such a subextension, membership in a valuation ring can be tested on a power, and uniqueness of the extension of the valuation at a finite level forces `K`-automorphisms of `Ω` to preserve membership on that level.

## Main definitions and results

- `ValuationSubring.mem_iff_pow_mem`: for a valuation ring `A` of a field and `n > 0`, `x ∈ A` iff `x^n ∈ A`; `mem_of_pow_mem` and `pow_mem_iff_mem` restate it.
- `restrictIntermediateField A E`: the valuation ring `A ∩ E` of an intermediate field `E`, as the preimage of `A`.
- `restrictIntermediateField_hasExtension`: if `A` extends a valuation `v` of `K`, so does its restriction to `E`. `smul_hasExtension`: so does its translate `σ • A` by a `K`-automorphism `σ` of `Ω`; the restriction of `σ • A` or `σ⁻¹ • A` extends `v` as well.
- `mem_algEquiv_apply_iff_of_restrictIntermediateField_unique`: suppose every valuation ring of `E` extending `v` equals the restriction of `A`. Then for every `K`-automorphism `σ` and `x ∈ E`, `x ∈ A` iff `σ(x) ∈ A`. The proof applies the uniqueness to the restriction of `σ⁻¹ • A`.
- `mem_algEquiv_apply_iff_of_restrictIntermediateField_henselianUnique`: the same conclusion when the uniqueness is supplied as a `HenselianDVF` structure on `E` whose valuation ring is the restriction of `A` and which has the library's unique-extension property over a `HenselianDVF` structure on `K`.
- `exists_finite_separable_intermediate_pow_mem`: for `Ω / K` algebraic and `z ∈ Ω`, some `z^n` with `n > 0` lies in a finite separable intermediate field; in the proof `n` is a power of the exponential characteristic, since `Ω` is purely inseparable over the separable closure of `K` in `Ω`.
- `exists_pow_isSeparable_of_isAlgebraic`: some positive power of `z` is separable over `K`.

## Watch for

The invariance statements take uniqueness of the extension at the finite level as a hypothesis; they do not prove it from a Henselian property of `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `8278eeec840f1957416f28392214572f10574cb6a51c63031b574991a967ad61`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
