# Functoriality of normalized valuations

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given a henselian valuation `v` (a `ValuationData`) on a `ℤ`-representation `A` of `G`, the file proves the two functorial properties of the normalized valuations `v_K`: compatibility with conjugation of fields, and the norm–valuation formula in a finite extension.

## Main results

- `DegreeData.fieldImage_conjugate`: the conjugate field `K^σ`, represented by `σ⁻¹ G_K σ`, has the same degree image as `K`.
- `DegreeData.FiniteResidueAbstractField.conjugate` and `FiniteAbstractField.conjugate`: conjugation of fields with finite residue quotient, resp. finite over the base, keeping the finiteness data; the `residueDegree_conjugate` lemmas show the residue degree is unchanged.
- `ValuationData.normalizedValuation_conjugate`: for `K` finite over the base (`FiniteAbstractField`) and `a ∈ A_K`, the normalized valuation of `K^σ` at `a^σ` equals `v_K(a)`, where `a^σ = σ⁻¹ a`.
- `ValuationData.normalizedValuation_tower`: for a finite extension `L | K` of fields finite over the base, `f(L/K) · v_L(a) = v_K(N(L/K)(a))` in `ℤ̂`.

## Proofs

For conjugation: the residue degrees agree, the norm to the base of `σ⁻¹ a` is `σ⁻¹ N(K/k)(a)`, and `N(K/k)(a)` is fixed by all of `G`. For the tower formula: after multiplying by `f_K`, use `f(L/K) · f_K = f_L` and transitivity of norms in the tower `k ⊆ K ⊆ L`.

## Points to watch

- Conjugation results assume `ContinuousMul G`, and conjugation is on the right.
- The tower formula is stated with the coercion to `ℤ̂` of values in `Z`, with residue degree taken from the enriched extension `toFiniteResidueAbstractExtension`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`: the Lean file is the source byte for byte (SHA-256 `1541a23b01ff05c80f47800062d3af8204ae68dc7ca89b33049ffa1951d6620e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
