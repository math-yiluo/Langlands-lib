# Conductor one characterizes unramified abelian extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension L/K of nonarchimedean local fields, the file proves that L/K is unramified if and only if its local conductor ideal is 1, equivalently its conductor exponent is 0. By `localConductorIdeal_eq_one_iff`, used here, conductor ideal 1 is equivalent to every unit of 𝒪_K being a norm from L.

## Main definitions and results

- `normQuotientFiniteOfIsAbelianGalois` and `card_normQuotient_eq_finrank_of_isAbelianGalois`: for K : Type u, L : Type v, L/K finite abelian Galois (no local-field structure on L needed), K^×/N(L^×) is finite of order [L:K]; this comes from the isomorphism with Gal(L/K) induced by the universe-polymorphic Artin map `Universe.abelianLocalArtinMonoidHom`.
- `chosenNormQuotientEquivZModResidueFinrank_of_fieldPrincipalUnits_zero_le`: for L/K Galois with `IsIntegralClosure 𝒪[L] 𝒪[K] L`, if all units of 𝒪_K are norms (`hU`), then K^×/N(L^×) ≃ ℤ/fℤ, f the residue degree; no unramified hypothesis.
- `fieldPrincipalUnits_zero_le_normSubgroup_of_unramifiedValuation`: in an unramified abelian extension every unit of 𝒪_K is a norm.
- `localConductorExponent_eq_zero_of_unramifiedValuation`, `localConductorIdeal_eq_one_of_unramifiedValuation`.
- `isFiniteUnramifiedValuationExtension_of_localConductorIdeal_eq_one`: conductor ideal 1 implies `IsUnramifiedValuedExtension K L`.
- `isFiniteUnramifiedValuationExtension_iff_localConductorIdeal_eq_one`, `isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero` and `not_isUnramifiedValuedExtension_iff_localConductorExponent_ne_zero`: the equivalences.

For the conductor statements: K and L nonarchimedean local fields, L/K finite abelian Galois, the valuation of L extending that of K, `IsIntegralClosure 𝒪[L] 𝒪[K] L` and `Module.Finite 𝒪[K] 𝒪[L]`.

## Proof

Unramified ⇒ conductor one: the norm subgroup consists of the elements with valuation divisible by [L:K], so it contains all units. Conductor one ⇒ unramified: the norm quotient has order f by the formula v_K(N y) = f · v_L(y), and order [L:K] by finite local reciprocity; with e · f = [L:K] and f > 0 this forces e = 1.

## Caveats

The direction "conductor one ⇒ unramified" depends on finite local reciprocity, through the order of the norm quotient.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/UnramifiedConductor.lean`: the Lean file is the source byte for byte (SHA-256 `19e4aec561f104ff0bcd4036643b10640e3564321bb1b4591605364fe0d8c589`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
