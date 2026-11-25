# Henselian valuations and normalized valuations

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The coefficient module is a `ℤ`-representation `A` of `G`, written additively, so valuations and norms are additive homomorphisms. The file defines a henselian valuation of `A_k` (the elements fixed by all of `G`) with respect to a degree datum `d`, by a valuation-quotient axiom, and builds for every abstract field `K` finite over the base the normalized valuation `v_K = (1/f_K) · v ∘ N(K/k)`.

## Main definitions and results

- `normToBase`: the norm `N(K/k) : A_K → A_k`, the relative norm to the base field.
- `nsmulWithin Z n` and `nsmulImage Z n`: the subgroup `nZ`, inside `Z` and inside `ℤ̂`. `canonicalValueQuotientMap Z n`: the map `Z/nZ → ℤ/n` induced by the inclusion `Z ≤ ℤ̂` and reduction mod `n`; `canonicalValueQuotientMap_top_bijective` proves it bijective for `Z = ℤ̂`.
- `ValuationData D A`: an additive homomorphism `v : A_k → ℤ̂` such that (i) every integer is a value, and the canonical map `Z/nZ → ℤ/n` is bijective for every `n > 0`, where `Z = v(A_k)`; (ii) for every `K` finite over the base, `v(N(K/k)(A_K)) = f_K · Z`.
- `valueGroup` (`Z`), `cyclic_value_quotients` (`Z/nZ ≃ ℤ/n`), `valueModulo` and `valueModulo_surjective`.
- `normCompositeAt` (`v ∘ N(K/k)`), `dividedAt` (its quotient by `f_K` in `ℤ̂`) and `valuationAt` (`v_K : A_K → Z`). `residueDegree_nsmul_dividedAt` gives `f_K · v_K = v ∘ N(K/k)`, and `dividedAt_mem_valueGroup` that the quotient lies in `Z`.
- `normalizedValuation_surjective`: `v_K` maps onto `Z`.
- `FiniteAbstractField.normToBase_index_eq_degree`: the index used by the norm is the degree of `K`.

Division by `f_K` is legitimate because condition (ii) puts `v ∘ N(K/k)` inside `f_K ℤ̂`, where multiplication by `f_K` is invertible.

## Points to watch

- `ValuationData` is a bundle of hypotheses: condition (ii) on norm images is a field of the structure, not a theorem, and every result on `v_K` depends on it.
- Values lie in `ℤ̂`, not `ℤ`. The value group `Z` is a subgroup of `ℤ̂` containing `ℤ`, and the quotient condition concerns the specific reduction map, not just an abstract isomorphism `Z/nZ ≃ ℤ/n`.
- Normalized valuations are defined only for fields finite over the base (`FiniteAbstractField`), whose residue degree is a positive natural.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`: the Lean file is the source byte for byte (SHA-256 `e3d21d7f5a09bc94b90c688d7e636fa658dc4a1fbe24b98f16362956dfb4c9d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
