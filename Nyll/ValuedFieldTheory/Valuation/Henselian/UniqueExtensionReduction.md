# Reduction of irreducible factors under unique extension of a valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `V` be a valuation subring of a field `K`. The file shows that when `V` extends uniquely, the reduction of a monic irreducible factor never splits into two coprime nonconstant pieces, and uses this to lift a coprime factorization of a product of reductions to `V`.

## Main results

Below, `W` is a valuation subring of an extension field `L` of `K` with `V.valuation.HasExtension W.valuation` (Mathlib's `Valuation.HasExtension`), and `F̄` is the reduction of `F`.

- `monic_splits_in_extension_valuationSubring`: a monic `F` over `V` that splits over `L` splits over `W`; by `monic_reduction_splits_in_extension_residueField`, `F̄` then splits over the residue field of `W`.
- `monic_eq_prod_monic_irreducible_map_factors`: every monic `f` over `V` is a product of monic polynomials over `V` irreducible over `K`.
- `residues_of_irreducible_roots_are_conjugate`: if `L/K` is normal, `W` is the only extension of `V` to `L`, and `a, b ∈ W` are roots of an `F` irreducible over `K`, some `σ ∈ Aut_K(L)` induces a residue automorphism sending the residue of `b` to that of `a`.
- `irreducible_monic_reduction_coprime_factor_degree_zero`: if `F` is monic over `V`, irreducible over `K`, `L` is its splitting field and `W` is unique, then in any factorization `F̄ = ḡ · h̄` into coprime factors one factor has degree 0. `irreducible_monic_reduction_dvd_left_or_right_of_coprime`: in that setting, if `F̄` divides `ḡ · h̄` with `ḡ, h̄` coprime, it divides `ḡ` or `h̄`.
- `partition_monic_irreducible_factors_along_coprime_reduction`: if `V` extends uniquely to every algebraic extension of `K`, and a multiset of monic factors, each irreducible over `K`, has product of reductions `ḡ · h̄` with `ḡ, h̄` monic and coprime, then the product of the factors is `G · H` with `G, H` monic over `V`, `Ḡ = ḡ`, `H̄ = h̄`.

## Proofs

Roots of a monic polynomial over `V` are integral over `V`, hence lie in `W`. If `ḡ` and `h̄` both had positive degree, roots `γ` of `ḡ` and `δ` of `h̄` lift to roots of `F` in `W`; conjugacy gives a residue automorphism fixing the residue field of `V` and sending `γ` to `δ`, so `δ` is a root of `ḡ`, against coprimality. The partition result is an induction on the multiset.

## Points to watch

- Uniqueness of the extension is a hypothesis, not derived here: `huniq` says every valuation subring of `L` extending `V` equals `W`; `hunique` asks for a unique extension to every algebraic extension of `K` in the universe of `K`.
- The degree and divisibility results need an `IsSplittingField` instance for `L`.
- Lifting a factorization of an arbitrary monic polynomial, by combining the partition result with the factorization into irreducibles, is not done in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/UniqueExtensionReduction.lean`: the Lean file is the source byte for byte (SHA-256 `ae012f9a82485483cec3eae5b067f30ca645417d8adfb8b980a5c7303b25b507`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
