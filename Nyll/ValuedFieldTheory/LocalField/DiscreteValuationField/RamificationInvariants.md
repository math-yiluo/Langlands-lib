# Ramification index, residue degree and the fundamental identity n = e·f

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `base` and `target` be fields K and L with chosen complete discrete valuations (the library's `CompleteDVF`), L an algebra over K, and the valuation of L extending that of K. For the library's invariants of the extension of valuation rings, the ramification index e, the residue degree f and the degree n (`ValuedExtension.ramificationIndex`, `residueDegree`, `degree`), the file collects the identity n = e·f and its consequences, first under a finiteness hypothesis on the valuation rings and then for finite separable L/K.

## Main results

- `degree_eq_ramificationIndex_mul_residueDegree`: n = e·f, assuming O_L is a finite O_K-module and the scalar tower O_K → O_L → L.
- `ramificationIndex_ne_zero` and `ramificationIndex_pos`: e > 0, assuming O_L is torsion-free over O_K. `residueDegree_ne_zero` and `residueDegree_pos`: f > 0, assuming O_L is finite over O_K.
- `ramificationIndex_le_degree`, `residueDegree_le_degree`: e ≤ n and f ≤ n under the hypotheses of the identity (the latter also needs torsion-freeness).
- Under the hypotheses of the identity: `degree_eq_one_iff_ramificationIndex_eq_one_and_residueDegree_eq_one` (n = 1 iff e = 1 and f = 1), `residueDegree_eq_degree_of_ramificationIndex_eq_one` (e = 1 implies f = n), `ramificationIndex_eq_degree_of_residueDegree_eq_one` (f = 1 implies e = n).
- `isUnramified_iff_ramificationIndex_eq_one` and `isTotallyRamified_iff_residueDegree_eq_one`: these unfold the library's predicates `IsUnramified` and `IsTotallyRamified`.
- For finite-dimensional separable L/K, still assuming the scalar tower O_K → O_L → L: `degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable` (n = e·f), `isDefectless_of_finite_separable`, the bounds e ≤ n and f ≤ n, and the equivalences e = 1 ⇔ f = n and f = 1 ⇔ e = n, also stated as characterizations of `IsUnramified` and `IsTotallyRamified`.

## Proofs

The identities are taken from results proved elsewhere in the library (`ramificationIndex_mul_residueDegree_eq_degree` and its separable form); in the separable case, finiteness and torsion-freeness of O_L over O_K are supplied by the library's lemmas for finite separable extensions. The rest is arithmetic with positive integers.

## Points to note

- `IsUnramified` means only e = 1, as its docstring states: it is the weak notion and does not require the residue extension to be separable. A stronger notion `IsFiniteUnramified` is mentioned but not used here.
- `IsTotallyRamified` is by definition f = 1.
- Outside the separable section, the identity n = e·f is not proved from the field data: it takes finiteness of O_L over O_K as a hypothesis.
- e, f and n are the library's own definitions (namespace `ValuationTheory.DiscreteValuationField.ValuedExtension`) for the chosen valuation rings; their definitions are not in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`: the Lean file is the source byte for byte (SHA-256 `ea668f49c08172a5d16e5ee9461653e1d04cf100f9ea18f52bc07bf5c988a6f7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
