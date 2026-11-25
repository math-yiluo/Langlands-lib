# The standard Lubin–Tate formal group and its endomorphisms

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let π be a uniformizer of a local field K and f = π·X + X^q the standard Lubin–Tate series. The file builds from the unique intertwiners of the recursive-intertwiner file the commutative formal group law F_f over the valuation ring, with F_f(f(X), f(Y)) = f(F_f(X, Y)), and the endomorphisms [a] for every a in the valuation ring. All structural identities are proved from uniqueness of an intertwiner with given linear term. The file also proves that intertwiners are stable under substitution.

## Main definitions

In `LubinTate.SameUniformizer`:

- `standardFormalGroupPowerSeries hπ`: the unique two-variable series with zero constant coefficient and linear term X + Y intertwining f with itself.
- `standardFormalGroup hπ`: the corresponding Mathlib `FormalGroup` over the valuation ring, with instance `standardFormalGroup_isComm`.
- `standardLubinTateEndomorphism hπ a`: the unique one-variable series [a] with zero constant coefficient and linear coefficient a commuting with f.
- `standardLubinTateEndomorphismInVariable hπ a i`: [a](Xᵢ).

## Main results

- `HasLinearTerm.coeff_eq_linearForm`, `HasLinearTerm.coeff_single`, `HasLinearTerm.subst`, `hasLinearTerm_X`, `hasLinearTerm_zero`: linear terms are read off coefficientwise, and multiply as matrices under substitution.
- `subst_powerSeries_subst`, `subst_inVariable`, `Intertwines.subst`, `Intertwines.reindex`, `Intertwines.powerSeries_subst`, `intertwines_zero`: substituting a family of intertwiners for ē, ê into an intertwiner for e, ē gives an intertwiner for e, ê; renaming variables and composition preserve intertwiners; 0 intertwines.
- `standardFormalGroupPowerSeries_hasLinearTerm`, `_intertwines`, `existsUnique_standardFormalGroupPowerSeries`: the defining properties.
- `standardFormalGroupPowerSeries_subst_X_zero`, `_subst_zero_X`: F(X, 0) = X and F(0, Y) = Y.
- `standardFormalGroupPowerSeries_assoc`, `standardFormalGroupPowerSeries_comm`: associativity and commutativity.
- `standardLubinTateEndomorphism_coeff_one`, `existsUnique_standardLubinTateEndomorphism`: [a] has linear coefficient a and is unique.
- `standardLubinTateEndomorphism_one`, `_zero`: [1] = X and [0] = 0.
- `standardLubinTateEndomorphism_add`: [a + b] = F([a], [b]).
- `standardLubinTateEndomorphism_mul`: [ab] = [a] ∘ [b].
- `standardLubinTateEndomorphism_map_formalGroup`: [a](F(X, Y)) = F([a](X), [a](Y)).

## Proofs

Each identity compares two series that both intertwine f with itself and have the same linear term; the substitution-closure results and `HasLinearTerm.subst` supply these two facts, and uniqueness finishes.

## Watch for

- The formal group and the endomorphisms [a] are built only for the standard series π·X + X^q, while the substitution results hold for arbitrary Lubin–Tate series for the same π; the formal group of a general Lubin–Tate series and the comparison of different series or different uniformizers are not in this file.
- `Intertwines.subst`, `Intertwines.reindex` and `Intertwines.powerSeries_subst` assume finite variable types and `PowerSeries.HasSubst H`; the first and the last also assume `MvPowerSeries.HasSubst G`, respectively `PowerSeries.HasSubst G`, for what is substituted.
- The ring structure a ↦ [a] is given by these identities; the file does not package it as a ring homomorphism into the endomorphism ring of a formal group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`: the Lean file is the source byte for byte (SHA-256 `ddac378f69df0a826fa87a38782245af22819c3d4de2e7855506f44d72c44dc4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
