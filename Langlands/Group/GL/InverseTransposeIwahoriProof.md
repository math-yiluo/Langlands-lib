# Inverse-transpose transport of block Iwahori data

Author: Worker 363.

The theorem `Langlands.GeneralLinear.BlockShape.inverseTransposeIwahori`
proves exactly the published proposition
`Langlands.GeneralLinear.BlockShape.InverseTransposeIwahoriStatement` from
`Langlands.Group.GL.InverseTransposeIwahoriStatement`. It retains the full
universe-polymorphic telescope: every prime `p`, its primality instance, every
`F : PadicField.{u} p`, every supplied `T : F.TopologicalData`, every natural
rank `n`, and every `B : BlockShape n`. The statement and all imported modules
are used unchanged.

The proof uses the existing inverse transpose, actual radicals, embedded common
Levi, block scalars, and `HasBlockIwahoriFactorization`. No conclusion of the
transport statement is assumed. There are no extra rank, properness, chamber,
compactness, representation, or admissibility assumptions. Rank zero, the empty
shape, and one-block shapes remain included. The first four results below hold
more generally over every commutative ring `R : Type u`.

## Named results

All these names are in `Langlands.GeneralLinear.BlockShape`.

| Theorem | Published clause proved |
| --- | --- |
| `inverseTranspose_unipotent_map B R` | `InverseTransposeUnipotentClause B R` |
| `inverseTranspose_oppositeUnipotent_map B R` | `InverseTransposeOppositeUnipotentClause B R` |
| `inverseTranspose_levi_map B R` | `InverseTransposeLeviClause B R` |
| `inverseTranspose_blockScalar B R` | `InverseTransposeBlockScalarClause B R` |
| `inverseTranspose_compact_comap T n` | `InverseTransposeCompactComapClause T n` |
| `inverseTranspose_iwahoriFactorization T B` | `InverseTransposeIwahoriFactorizationClause T B` |

Three additional membership equivalences expose the pointwise radical and Levi
transport: `inverseTranspose_mem_oppositeUnipotentSubgroup_iff`,
`inverseTranspose_mem_unipotentSubgroup_iff`, and
`inverseTranspose_mem_leviSubgroup_iff`.

## Algebraic transport

Write `e = inverseTranspose n R`, so `e(g) = (g⁻¹)ᵀ` and `e(e(g)) = g`.
For an upper radical element `g`, subgroup inversion shows that `g⁻¹` is again
upper radical. Its diagonal blocks are identity matrices. Transposition swaps
its block entries and leaves these identity blocks unchanged. The existing
`inverseTranspose_mem_oppositeParabolic_iff` supplies lower-parabolic membership.
This proves upper-to-lower transport. The same argument with the opposite
radical proves lower-to-upper transport. Involutivity gives the two membership
biconditionals; `Subgroup.mem_map_equiv` turns them into subgroup image
equalities.

For the common Levi, the private embedding calculation identifies the inverse
transpose of `B.leviEmbedding R m` with the embedding of the tuple
`fun i => inverseTranspose (B.size i) R (m i)`. The proof checks diagonal blocks
and off-diagonal blocks separately, using the existing embedding entry formulas
and its inverse law. Hence the embedded Levi is preserved; involutivity supplies
the converse and thus equality of its image with itself.

For block scalars, the homomorphism inverse law rewrites the inverse scalar
matrix as `B.blockScalar R a⁻¹`. Its matrix is diagonal by the existing
`coe_blockScalar` theorem, and a diagonal matrix equals its transpose. The result
is `e(B.blockScalar R a) = (B.blockScalar R a)⁻¹` for every tuple `a`.
The tuple in this result is the original `a`; no contraction condition on its
inverse is involved.

## Compactness for the supplied topology

The proof installs precisely `T.topology`. The existing
`T.generalLinearInverseTranspose n` is a continuous multiplicative equivalence,
whose homeomorphism is a closed embedding. The closed-embedding compact-preimage
theorem therefore proves compactness of the underlying set of the actual
`OpenSubgroup.comap`. Openness is already part of that existing construction.
No auxiliary topology or additional separation hypothesis is introduced.

## Bijectivity of the ordered product

The private algebraic proof works first with any subgroup `K`, and sets
`K' = K.comap e.toMonoidHom`. It uses the involutive map

`f(g) = e(g⁻¹)`.

This map reverses multiplication: `f(x*y) = f(y)*f(x)`. It is used only to
construct internal equivalences between subgroup carriers. Inversion is legal
because every factor is a subgroup. The radical and Levi membership results
then give equivalences from the lower, Levi, and upper intersections with `K'`
to the upper, Levi, and lower intersections with `K`, respectively. The same
map gives an equivalence `q : K' ≃ K`.

The proof combines these equivalences into a triple equivalence `t` sending
`(l,m,u)` to `(f(u),f(m),f(l))`. If `P_K` and `P_K'` denote the published ordered
products, the group inverse and homomorphism laws prove

`P_K(t(x)) = q(P_K'(x))`.

For injectivity, equal products under `P_K'` give equal products under `P_K`;
the assumed injectivity of `P_K`, followed by injectivity of `t`, gives equality
of the original triples. For surjectivity, factor `q(y)` using surjectivity of
`P_K`, apply `t.symm` to its triple, and use injectivity of `q` to show that its
product is `y`. This proves full bijectivity, including uniqueness, in the
original lower-Levi-upper order.

## Both containments at the same weak tuple

For the open comap and a tuple `a` satisfying `B.IsWeaklyContracting T a`, put
`s = B.blockScalar F.Carrier a`. The scalar identity and homomorphism laws give

- `e(s*g*s⁻¹) = s⁻¹*e(g)*s`;
- `e(s⁻¹*g*s) = s*e(g)*s⁻¹`.

If `g` belongs to the upper intersection with the comap, then `e(g)` belongs to
the lower intersection with `K`. The original lower inverse-conjugation
containment, applied to exactly `a`, supplies membership in `K` of the first
displayed image. The existing scalar normalization of the upper radical
supplies its radical membership. These two facts give the new upper
containment. The proof uses the original upper containment and the existing
opposite-radical normalization in the same way for the new lower containment.
Both directions retain the same weak tuple and its given chamber proof.

Combining these containments with the product bijection proves the unchanged
`HasBlockIwahoriFactorization` predicate for the actual open comap. Compactness
is proved separately and is not assumed in the factorization theorem. The
closing theorem assembles the six results in the published conjunction order.

## Provenance and scope

This is an internal derived proof from the published definitions and elementary
matrix, group, and topological laws. The implementation follows the transport
argument described in `InverseTransposeIwahoriStatement.md`, with the
factorization transfer made explicit by carrier equivalences and a commuting
product identity. Existing results are imported by their Lean names; no matrix
map, block geometry, or Iwahori predicate is reconstructed.

The statement module records the historical motivation from Casselman's
Chapter III, revision April 29, 2019, sections 4–6, especially III.5.4–III.5.5
on pages 6–7 (`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`).
That source motivates the Iwahori and canonical-lift setting; the present
inverse-transpose argument is an internal derivation, and the stronger weak
chamber remains the project's published specialization as explained in
`BlockIwahoriDefinitions.md`. This module proves neither an opposite canonical
lift nor a final pairing theorem.
