# Irreducible factors of a polynomial and conjugacy classes of its roots

Module `Nyll.ValuedFieldTheory.Valuation.Completion.PolynomialFactors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The algebra behind the correspondence between extensions of a valuation and irreducible factors over the completion. For a nonzero polynomial `p` over a field `F` and an algebraically closed algebraic extension `E`, the classes of roots of `p` in `E` with the same minimal polynomial correspond to the distinct monic irreducible factors of `p`. Multiplicities of factors are discarded.

## Main definitions and results

- `polynomialNormalizedFactors`: Mathlib's `normalizedFactors`, with the classical decidable equality installed inside the definition; `polynomialDistinctNormalizedFactors`: its underlying finite set; `DistinctNormalizedFactors p`: the corresponding subtype. Both depend only on the associate class of `p`.
- `PolynomialRootsIn E p`, `rootMinpoly`, `rootMinpolySetoid`: roots of `p` in `E`, the map sending a root to its minimal polynomial over `F`, and the equivalence relation "same minimal polynomial".
- `rootMinpoly_mem_normalizedFactors` and `range_rootMinpoly_eq_distinctNormalizedFactors`: the minimal polynomials of roots are exactly the distinct normalized factors (the second needs `E` algebraically closed).
- `rootClassesEquivDistinctNormalizedFactors`: the resulting bijection.
- `rootMinpolySetoid_rel_iff_isConjRoot`, `rootMinpolySetoid_rel_iff_orbitRel`: the relation is `IsConjRoot`, and for `E / F` normal it is the orbit relation of `Gal(E / F)`.
- `simpleEmbeddingsEquivMappedMinpolyRoots`: for `L = K(α)` with `α` integral, `K`-embeddings of `L` into a field `E` over `K'` correspond to roots in `E` of the minimal polynomial of `α` mapped to `K'[X]`, via `τ ↦ τ α`.

## Points to watch

The bijection with factors requires `E` algebraic over `F` and algebraically closed; for an algebraic `E` that is not algebraically closed, only the inclusion of minimal polynomials among the factors is proved.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/PolynomialFactors.lean`: the Lean file is the source byte for byte (SHA-256 `1d75840ff45e51bfd4a8a654bffb0d9f746845c2cf01b10e1d53dbab955ffb07`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
