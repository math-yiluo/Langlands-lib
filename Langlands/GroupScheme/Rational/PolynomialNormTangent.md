# Nonzero differentials of scalar-parameter central Galois norms

This is an internal construction from the existing polynomial norm, actual
Lie kernels, and independence of field automorphisms. It proves that a
monomorphic central vector-group input of positive dimension has a scalar
norm with nonzero differential over the base field. No assertion about the
scheme-theoretic image or split-unipotence descent is made here.

Let `k` be a field, `L/k` a finite Galois extension, and `G` an affine group
scheme over `k`. Put `G_L = G ×_k L`. Given a central homomorphism
`f : G_a,L^n → G_L`, the preceding `PolynomialNormInput` construction provides
`normOfCentralHom k L G f hf a : G_a,k^n → G` for each `a : L`. The scalar
multiplies the input coordinates over `L` before taking the Galois product.

## Actual tangent points and the input tangent

`vectorTangent v` is the actual identity-kernel point of the standard vector
group over `A[ε]`, obtained by evaluating its universal polynomial point
at `(ε v_i)`. It belongs to the kernel because reduction evaluates at zero,
and an additive polynomial point takes zero to the identity. The lemma
`vectorCoordinates_vectorTangent` recovers exactly the pure-epsilon tuple.
`vectorCoordinates_one` follows from multiplicativity of the coordinate
comparison, and `vectorTangent_ne_one` detects any nonzero coordinate.
Coefficient maps act coordinatewise, and postcomposition by an actual
homomorphism is polynomial evaluation at the same tuple.

For a base-field tuple `v : Fin n → k`, `epsilonEvaluation k L v` is the
`k`-algebra map `L[X_i] → L[ε]` taking `X_i` to `ε algebraMap(v_i)` while
retaining constants in `L`. Its composition with a coefficient automorphism
`σ` equals coefficient change by `σ` after evaluation. This uses that `v`
is base-field valued. Its composition with polynomial coefficient extension
also equals extension of the actual base-field dual-number evaluation.
Both comparisons are proved on constants and variables.

`inputTangent k L G f v` first applies the actual identity-kernel target map
of `f` to the vector tangent over `L`, then uses the actual kernel
base-change equivalence to view it in `Lie(G)(L)`. Evaluation of
`centralInput` at the epsilon tuple is its underlying dual-number point.
Evaluation of `scalarCentralInput` is epsilon scaling by `a` of this tangent;
the proof compares the corresponding algebra maps and uses naturality of
the affine base-change equivalence. These input and evaluation identities
require neither affineness of `G` nor finiteness or Galoisness of `L/k`.

If the underlying scheme morphism of `f` is monomorphic, postcomposition is
injective on actual Lie kernels. The base-change equivalence is injective
as well. Consequently `inputTangent_ne_zero` shows that a nonzero
base-field coordinate direction gives a nonzero input tangent.

## Differential of the norm

With affine `G` and finite Galois `L/k`,
`normOfCentralHom_tangent_product` evaluates the full conjugate-product
extension formula on the epsilon tuple. Evaluation preserves each finite
product; a finite-set induction compares the central-point product with
the product in the actual identity kernel. The evaluation/automorphism
comparison identifies each factor as the coefficient conjugate of the
scaled input tangent.

Writing the kernel group law additively gives
`normOfCentralHom_tangent_sum`. If `w = inputTangent k L G f v`, its formula is

```text
extension of d(norm_a)(v) = Σ_σ σ(a) · σ_*(w).
```

Here `σ_*` is the actual semilinear coefficient map on the Lie kernel.
The scalar `σ(a)` follows from its semilinearity. The left side starts with
a tangent over `k` and then changes its coefficients to `L`.

## Nonvanishing and the selected homomorphism

`exists_galois_smul_sum_ne_zero` applies to any `L`-module and any family
`w_σ` indexed by the automorphisms of `L/k`, with one nonzero member.
A separating linear functional turns hypothetical vanishing for every `a`
into a linear relation among the functions `a ↦ σ(a)`. The existing
`Descent.galoisFunctions_linearIndependent` forces every coefficient to
vanish, contradicting the chosen functional. This lemma only needs
finite dimensionality of `L/k`, not Galoisness.

The identity coefficient automorphism acts identically on the actual
kernel. Applying the preceding independence lemma to `σ_*(w)` therefore
shows that some scalar norm has nonzero value on `v` when `w ≠ 0`.
If `n > 0` and `f` is monomorphic, choose the first standard coordinate
vector and use `inputTangent_ne_zero` to obtain this conclusion.

`nonzeroNormOfCentralHom` chooses such a scalar norm and returns an actual
homomorphism `q : G_a,k^n → G`, together with `IsCentral q` and
`Lie.targetMapLinear q k ≠ 0`. Centrality is the existing full center
condition on every refinement of every scheme test. Nonvanishing of the
linear map follows by evaluating a hypothetical zero map on the chosen
vector tangent.

Every field and characteristic is retained, including finite and imperfect
fields. There is no division by the extension degree. The construction does
not assume `G` smooth, connected, commutative or unipotent. Obtaining a
smooth connected split image, descending split unipotence, and proving the
host maximal-torus conjugacy statement remain separate obligations.
