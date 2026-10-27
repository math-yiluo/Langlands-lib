# Compression identities for the upper refined radical of a product Levi

Author: Worker 246.

This module proves one theorem, `Langlands.Jacquet.refinedUpperCompression`. It is
the upper-radical form of the published `refinedOppositeCompression`, which is the
proof of `RefinedOppositeCompressionStatement`. No definition or statement is
introduced.

## Statement

The parameters are a prime `p`, `F : PadicField.{uF} p`, `T`, a block shape
`B : BlockShape n`, a refinement `S : BlockRefinement B` and a complex carrier
`V : Type uV`. The topologies are `T.topology` and `T.leviTopologicalGroup B`.
The theorem takes a smooth representation `ρ` of `B.Levi F.Carrier` on `V` and
compact open subgroups `K i` of the factors with
`(S i).HasBlockIwahoriFactorization T (K i)`. Let `KP` be
`CuspidalSupport.leviPiOpenSubgroup T B K` and `C(g)` the published
`Jacquet.compressedAction ρ hρ KP hKP g`, the normalized compact average after
acting by `g`, on the `KP`-fixed vectors. The theorem asserts the following.

1. For nested scalar tuples `a b : ∀ i, Fin (S i).length → F.Carrierˣ` that are
   blockwise `IsWeaklyContracting`, with `g(a) = fun i => (S i).blockScalar F (a i)`,
   one has `C(g(a * b)) = C(g(a)) * C(g(b))`.
2. For such `a` and every fixed vector `v`, the actual quotient map onto the
   coinvariants by `refinedUnipotent F.Carrier B S` satisfies
   `mk (C(g(a)) v) = mk (ρ (g(a)) v)`.

Weak contraction means `|a_k / a_l| ≤ 1` for `k < l` inside each outer block, so
`g(a)` contracts the upper refined radical.

## Proof

The proof is a transport by `leviInverseTranspose`, the blockwise inverse
transpose `e`, as in the published `RefinedUpperCanonicalLiftProof`.

- The comap subgroups `K'` have Iwahori factorizations by
  `BlockShape.inverseTranspose_iwahoriFactorization`.
  `leviInverseTranspose_map_leviPiOpenSubgroup` identifies `e(KP')` with `KP`.
- `refinedOppositeCompression` applied to `ρ ∘ e` gives both identities for the
  opposite radical and the elements `g(a)⁻¹`. The published
  `leviInverseTranspose_blockScalar_inv` shows that `e` maps these elements to
  `g(a)`.
- `compressedAction_groupTransport` conjugates the two compressed actions through
  `fixedVectorsGroupTransportEquiv`, which is the identity on vectors. This gives
  the multiplication law.
- `coinvariantsGroupTransportEquiv` sends `mk` for `ρ ∘ e` and the opposite
  radical to `mk` for `ρ` and its image, the upper radical
  (`leviInverseTranspose_refinedOppositeUnipotent_map`). This gives the quotient
  identity.

The quotient identity uses the unnormalized descended action; no modulus factor
enters.
