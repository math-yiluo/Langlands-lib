# Roots of unity of order q − 1 lift the residue units

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a field with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, and finite residue field k with q elements. The file shows, by Hensel's lemma, that reduction maps the group μ_(q−1)(O) of (q − 1)-st roots of unity in O isomorphically onto k^*: the Teichmüller representatives.

## Main definitions and results

- `residueRootsOfUnityGroup F`: the subgroup `rootsOfUnity (q − 1)` of O^*, with q = `Nat.card F.residueField`.
- `residueRootPolynomial_derivative_eval_ne_zero`: the derivative of X^(q−1) − 1 over k does not vanish at any nonzero element of k, since q − 1 = #k^* is nonzero in k; this is what makes these elements simple roots.
- `exists_residueRootsOfUnity_lift`: every y ∈ k^* is the residue of some u ∈ O^* with u^(q−1) = 1.
- `residueRootPolynomial_derivative_eval_isUnit`: the derivative of X^(q−1) − 1 at any unit of O is a unit.
- `residueRootsOfUnityResidueHom_injective`, `..._surjective`, `..._bijective`: reduction μ_(q−1)(O) → k^* is bijective.
- `residueRootsOfUnityEquivResidueFieldUnits F`: the resulting group isomorphism μ_(q−1)(O) ≃ k^*, given by reduction.

## Proofs

Existence uses the library's Hensel lemma for the Henselian DVR underlying `F` (`exists_monic_linear_factor_lift_of_reduced_simple_root`) applied to X^(q−1) − 1 at a simple residue root. Uniqueness uses the library's statement that two roots with the same residue coincide when the derivative at one of them is a unit.

## Points to note

- Finiteness of the residue field is an instance hypothesis throughout; the group is defined with the exponent q − 1 read from `Nat.card`, not from a chosen q.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/ResidueRoots.lean`: the Lean file is the source byte for byte (SHA-256 `3be2ee99e97f85cc751297413137cca44b773cb7d6280129cb93f5fd10c7ab26`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
