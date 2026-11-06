# Euler factors of finite direct sums of Weil–Deligne pairs

This module proves that rational L-factors of Weil–Deligne pairs are
multiplicative in finite direct sums, and that pair L-factors of two finite
direct sums are the product over all pairs of summands:
\[
  L\Bigl(\bigoplus_{i<r} B_i \otimes \bigoplus_{j<t} B'_j\Bigr)
    = \prod_{i<r}\prod_{j<t} L(B_i\otimes B'_j).
\]
Everything is algebraic. The coefficient field \(K\), group \(G\), norm
character \(\nu : G \to K^\times\), normal subgroup \(I\) and element
\(g \in G\) are arbitrary inputs; no topology, characteristic-zero or
semisimplicity hypothesis is used. Families are indexed by `Fin r`, and the
empty family (\(r = 0\)) is allowed: both sides are then \(1\).

The L-factors are the existing Library objects:
`WeilDeligne.eulerPolynomial A I g` is the reversed characteristic polynomial
\(\det(1 - X\,g)\) of `g` on the inertia-fixed monodromy kernel
`A.inertiaKernelRepresentation I` \(= (\ker N)^I\), `rationalLFactor A I g` is
its reciprocal in \(K(X)\), and `pairLFactor A B I g` is `rationalLFactor` of the
actual tensor pair `WeilDeligneRepresentation.tensor A B`, whose monodromy is
\(N_A \otimes 1 + 1 \otimes N_B\).

## Provenance

The results are the algebraic content of the product formula in Henniart 2002,
§2.1–2.2 (printed p.593, PDF p.7): for representations of the Weil–Deligne
group, \(L(s,\sigma_1\oplus\sigma_2) = L(s,\sigma_1)L(s,\sigma_2)\) and, for
\(\sigma = \sum_i \sigma_i\), \(\sigma' = \sum_j \sigma'_j\),
\(L(s,\sigma\otimes\sigma') = \prod_{i,j} L(s,\sigma_i\otimes\sigma'_j)\).
Here they are proved for the Library's pair L-factors with arbitrary \(K\),
\(G\), \(\nu\), \(I\), \(g\). The auxiliary definitions (`kernelSubtype`,
`kernelMk`, `kernelEquivOfEmbedding`, `directSumCoord`,
`directSumKernelEmbedding`, `tensorDirectSumLeft`, `tensorDirectSumRight`) are
internal infrastructure for these proofs. In the arithmetic setting,
`Langlands.Correspondence.arithmeticPairLFactor F X Y` is by definition
`pairLFactorClass (localInertia F) (localGeometricFrobenius F) X Y`, which on
representatives is `pairLFactor`, so `pairLFactor_eq_prod_of_equiv_directSum`
gives the arithmetic double-product formula for parameters equivalent to finite
direct sums.

## Linear algebra (namespace `Langlands.LocalFactor`)

- `eulerPolynomial_prodMap`: for endomorphisms \(f\), \(g\) of finite-dimensional
  spaces, the Euler polynomial of \(f \times g\) is the product. Proof: Mathlib's
  `LinearMap.charpoly_prodMap` and `Polynomial.reverse_mul_of_domain`.
- `eulerPolynomial_of_subsingleton`: on a zero space the Euler polynomial is
  \(1\) (the characteristic polynomial is monic of degree \(0\)).
- `eulerPolynomial_pi`: for a family \(f_i\) of endomorphisms indexed by `Fin r`,
  the componentwise operator `LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i` has
  Euler polynomial \(\prod_i \mathrm{Eul}(f_i)\). Proof by induction on \(r\):
  the empty product space is zero; for \(r+1\), conjugating by the inverse of
  `Fin.consLinearEquiv` turns the operator into
  \(f_0 \times (\text{operator on the tail})\), and `eulerPolynomial_conj`,
  `eulerPolynomial_prodMap` and the induction hypothesis conclude.
- `rationalFactor_eq_inv` (definitional) and `rationalFactor_pi`, the
  rational version, by `map_prod` and `Finset.prod_inv_distrib`.
- `directSumLeft_comp_map`, `directSumLeft_comp_monodromy` and the right-hand
  versions `directSumRight_comp_map`, `directSumRight_comp_monodromy`: Mathlib's
  distributivity isomorphisms `TensorProduct.directSumLeft` /
  `directSumRight` intertwine \(\bigl(\bigoplus_i f_i\bigr)\otimes h\) with
  \(\bigoplus_i (f_i \otimes h)\), and
  \(\bigl(\bigoplus_i f_i\bigr)\otimes 1 + 1\otimes h\) with
  \(\bigoplus_i (f_i\otimes 1 + 1\otimes h)\) (and symmetrically on the right).
  Proof: check on pure tensors and on each direct-sum component, using
  `directSumLeft_tmul` / `directSumRight_tmul`.

## Kernel embeddings (namespace `Langlands.LocalFactor.WeilDeligne`)

- `kernelSubtype A I` is the inclusion \((\ker N)^I \to A\); it is injective,
  lands in \(\ker N\), is fixed by \(I\), and the action of \(g\) on
  \((\ker N)^I\) (`kernelOperator A I g`) is the restriction of the action on
  \(A\) (`representation_kernelSubtype_of`). `kernelMk` builds an element of
  \((\ker N)^I\) from a vector killed by \(N\) and fixed by \(I\).
- `kernelEquivOfEmbedding φ ...`: if \(\varphi : W \to A\) is an injective
  linear map whose image consists of \(I\)-fixed vectors killed by \(N\), and
  every such vector is in the image, then \(W \simeq (\ker N)^I\).
- `eulerPolynomial_eq_of_embedding` / `rationalLFactor_eq_of_embedding`: if in
  addition \(g\,\varphi(w) = \varphi(T w)\) for an endomorphism \(T\) of \(W\),
  then the Euler polynomial (resp. rational L-factor) of \(A\) at \(g\) is that of
  \(T\). Proof: the equivalence conjugates \(T\) to `kernelOperator A I g`
  (checked after `kernelSubtype`), and `eulerPolynomial_conj` applies.

## Finite direct sums

For `A : Fin r → WeilDeligneRepresentation K G ν`, the carrier of
`WeilDeligneRepresentation.directSum A` is \(\bigoplus_i A_i\) with
componentwise action and monodromy.

- `directSumCoord A` is Mathlib's `DirectSum.linearEquivFunOnFintype`, the
  coordinates \(\bigoplus_i A_i \simeq \prod_i A_i\);
  `directSumCoord_monodromy` and `directSumCoord_representation` state that
  monodromy and action are computed coordinatewise (definitionally).
- `directSumKernelEmbedding A I` maps a family \((y_i)\), \(y_i\in(\ker N_i)^I\),
  to the vector with coordinates \(y_i\).
- `eulerPolynomial_directSum`: the Euler polynomial of the direct sum at \(g\)
  is \(\prod_i \mathrm{Eul}(A_i, I, g)\). Proof: apply
  `eulerPolynomial_eq_of_embedding` to `directSumKernelEmbedding` and the
  componentwise operator of the `kernelOperator (A i) I g`; injectivity,
  membership, surjectivity onto \((\ker N)^I\) and the intertwining property are
  checked coordinatewise; then `eulerPolynomial_pi`.
- `rationalLFactor_directSum`: the rational version.

## Tensor products and pair L-factors

- `tensorDirectSumLeft B C` is a genuine pair equivalence
  \(\bigl(\bigoplus_i B_i\bigr)\otimes C \simeq \bigoplus_i (B_i\otimes C)\), with
  underlying linear map `TensorProduct.directSumLeft`; the action and monodromy
  compatibilities are `directSumLeft_comp_map` and
  `directSumLeft_comp_monodromy`. `tensorDirectSumRight C B` is the analogous
  equivalence \(C\otimes\bigl(\bigoplus_i B_i\bigr) \simeq \bigoplus_i (C\otimes B_i)\).
- `pairLFactor_directSum_left` / `pairLFactor_directSum_right`: the pair
  L-factor is multiplicative in a finite direct sum in either argument, by
  invariance of `rationalLFactor` under pair equivalences
  (`rationalLFactor_eq_of_equiv`) and `rationalLFactor_directSum`.
- `pairLFactor_directSum_directSum`:
  `pairLFactor (directSum B) (directSum B') I g = ∏ i, ∏ j, pairLFactor (B i) (B' j) I g`,
  combining the two.
- `pairLFactor_eq_prod_of_equiv_directSum`: the same formula for any pairs
  \(A\), \(A'\) given with pair equivalences `directSum B ≃ A` and
  `directSum B' ≃ A'` (by `pairLFactor_eq_of_equiv`).
