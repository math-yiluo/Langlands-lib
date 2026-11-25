# Completed scalar endomorphisms of the p-adic Lubin–Tate groups

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file extends to the completed unramified Witt ring W of ℚ_p the scalar endomorphisms [a] (a in ℤ_p) of two Lubin–Tate formal groups: the multiplicative one, attached to the multiplicative Lubin–Tate series, and the standard one for the changed uniformizer u·p, u a unit of ℤ_p. It records their linear terms, composition law, invariance under Witt-vector Frobenius, and commutation with the Lubin–Tate series.

## Main definitions and results

- `padicCompletedMultiplicativeScalarEndomorphism p a`: the image in W⟦X⟧ of the series `recursiveIntertwiner` built from the multiplicative Lubin–Tate series with linear coefficient a.
- `padicCompletedChangedStandardScalarEndomorphism p u a`: the image in W⟦X⟧ of `standardLubinTateEndomorphism` for the changed uniformizer.
- Both have zero constant term and linear coefficient a (`..._constantCoeff`, `..._coeff_one`, `..._hasLinearTerm`), hence admit substitution (`..._hasSubst`).
- `powerSeries_hasLinearTerm_of_constantCoeff_coeff_one`: over any commutative ring, a one-variable series with zero constant term and X-coefficient a satisfies the library predicate `HasLinearTerm` with a.
- `..._mul`: [a·b] = [a] ∘ [b] for both families.
- `..._commutes`: [a] commutes under substitution with the completed multiplicative series, respectively the completed changed standard series.
- `..._frobenius`: the scalar endomorphisms, the completed multiplicative series and the completed changed standard series are fixed by Witt-vector Frobenius on coefficients.
- `padicCompletedChangedStandardScalarEndomorphism_uniformizer`: the endomorphism of the changed uniformizer itself is the completed changed standard series. `..._one`: the scalar 1 acts by X.

## Proofs

The composition and commutation laws over W are the images under the coefficient map of statements over ℤ_p. For the multiplicative family, [a·b] = [a] ∘ [b] follows from the uniqueness of intertwiners with a given linear term (`eq_of_hasLinearTerm_of_intertwines`). Frobenius invariance holds because the coefficients come from ℤ_p, on which Frobenius acts trivially (`padicValuationSubringToCompletedUnramifiedWittRing_frobenius`).

## Watch for

- The two families come from different constructions: the multiplicative one from `recursiveIntertwiner`, the changed one from `standardLubinTateEndomorphism`. `HasLinearTerm` is the library's own predicate.
- Composition is written with `PowerSeries.subst`: `subst B A` is A(B(X)).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/ScalarEndomorphisms.lean`: the Lean file is the source byte for byte (SHA-256 `dd4f14a5003dfe0e15be722d32a67239d41524463a7f7fa3c2a224275070d935`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
