# Semilinear maps of finite tensor products

Let `φ : R →+* R'` be a homomorphism of commutative semirings. For each index `i`, let `F i : s i → t i` be a `φ`-semilinear map from an `R`-module to an `R'`-module. This module constructs the induced `φ`-semilinear map of tensor products

`piTensorSemilinear φ F : (⨂[R] i, s i) →ₛₗ[φ] (⨂[R'] i, t i)`,

which sends `⨂ i, f i` to `⨂ i, F i (f i)`. Mathlib's `PiTensorProduct.map` covers only linear maps over a single ring. Here the coefficient ring may change along `φ`; for example `φ` can be a Galois automorphism of a field, or a field embedding. The index type is arbitrary and need not be finite. The universes of the index, the two rings and the two families are independent.

## Public declarations

All declarations are in the namespace `Langlands.PiTensorSemilinear`.

- `piTensorSemilinear φ F` is the induced semilinear map.
- `piTensorSemilinear_tprodCoeff` computes it on Mathlib's scaled generators `tprodCoeff R z f`: the value is `tprodCoeff R' (φ z) (fun i => F i (f i))`. This holds by definition.
- `piTensorSemilinear_tprod` (simp) computes it on pure tensors: `tprod R f ↦ tprod R' (fun i => F i (f i))`.
- `semilinear_ext` says that two `φ`-semilinear maps out of `⨂[R] i, s i` that agree on all pure tensors are equal.
- `piTensorSemilinear_id` says that if every `F i` is pointwise the identity, the induced map over `RingHom.id R` is the identity.
- `piTensorSemilinear_comp` is functoriality. Let `ψ ∘ φ = χ` (`RingHomCompTriple`) and suppose `H i x = G i (F i x)` for all `i` and `x`. Then `piTensorSemilinear ψ G` composed with `piTensorSemilinear φ F` is `piTensorSemilinear χ H`.

For families of algebras (`s i` an `R`-algebra and `t i` an `R'`-algebra):

- `piTensorSemilinear_one` and `piTensorSemilinear_mul` prove that the induced map preserves `1` and multiplication if every `F i` does.
- `piTensorRingHom F hF₁ hF` packages it as a ring homomorphism, with `piTensorRingHom_apply`.
- `reindex_mul` and `reindex_one` prove that Mathlib's reindexing equivalence `PiTensorProduct.reindex R s e`, for a bijection `e` of index types, preserves multiplication and `1`.

## Implemented proof

The map is built with Mathlib's `PiTensorProduct.liftAddHom` from the function `(z, f) ↦ tprodCoeff R' (φ z) (fun i => F i (f i))`. The five defining relations of the tensor product are checked directly:

- a zero factor maps to a zero factor (`zero_tprodCoeff'`);
- a zero coefficient maps to `φ 0 = 0` (`zero_tprodCoeff`);
- additivity in one factor uses `Function.apply_update` to move `F` through `Function.update`, then `add_tprodCoeff`;
- additivity in the coefficient uses `map_add φ` and `add_tprodCoeff'`;
- moving a scalar `r'` out of one factor uses `F i (r' • m) = φ r' • F i m`, `map_mul φ` and `smul_tprodCoeff_aux` over `R'`.

Semilinearity `piTensorSemilinear φ F (r • x) = φ r • piTensorSemilinear φ F x` follows by induction over `tprodCoeff` generators, using `smul_tprodCoeff'` and `map_mul φ`.

The value on a pure tensor follows from `tprod R f = tprodCoeff R 1 f` and `φ 1 = 1`. The extensionality lemma is induction over scaled pure tensors (`PiTensorProduct.induction_on`) with semilinearity. The identity and composition lemmas are immediate from extensionality and the value on pure tensors. Preservation of `1` is the value on the pure tensor `1 = tprod R 1` (`PiTensorProduct.one_def`). Multiplicativity is a double induction over scaled pure tensors, using Mathlib's `smul_tprod_mul_smul_tprod` and `map_mul φ`. Reindexing is handled in the same way with `reindex_tprod`.

## Sources and scope

This module is internal infrastructure for the tensor descent of conjugate algebras in J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13. There the Galois group acts on a tensor product of conjugate algebras by semilinear maps that permute the factors. The general semilinear tensor-product map is standard multilinear algebra and is not stated in that source. It is derived here from the universal property of `PiTensorProduct`.
