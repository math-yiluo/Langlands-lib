# Normalized opposite compression in product Levis

Author: Worker 166.

`Langlands.Jacquet.RefinedOppositeCompressionStatement.{uF,uV}` is a
Prop-valued definition stating two laws of the actual compact compressed
operator. This module does not prove those laws.

## Parameters and constructions

The proposition quantifies over every prime, a p-adic field `F : PadicField p`,
its supplied compatible `TopologicalData T`, every natural rank `n`, outer
block shape `B`, refinement `S`, and complex carrier `V : Type uV`. Field and
carrier universes are independent. It installs `T.topology` and the actual
product-Levi topological-group instance. The input is any smooth representation
`ρ` of `B.Levi F.Carrier` on `V`; neither admissibility nor finite-dimensionality
is required.

For each outer block `i`, `K i` is an actual compact open subgroup of
`GeneralLinear (B.size i) F.Carrier` satisfying
`(S i).HasBlockIwahoriFactorization T (K i)`. This is the published predicate:
the lower-Levi-upper multiplication map is bijective, and the two radical
intersections satisfy the specified conjugation containments for every weakly
contracting tuple.

`KP` is the published `CuspidalSupport.leviPiOpenSubgroup T B K`. Its underlying
subgroup is exactly `Subgroup.pi Set.univ (fun i => (K i).toSubgroup)`; its
openness comes from the finite product topology and `hKP` is supplied by
`isCompact_leviPiOpenSubgroup`. No alternative product identification is assumed.
The radical `N` is the actual `Geometric.refinedOppositeUnipotent F.Carrier B S`,
the product of the inner lower radicals.

For a family `a i : Fin (S i).length → F.Carrierˣ`, the local notation `g a`
means the actual element
`fun i => ((S i).blockScalar F.Carrier (a i))⁻¹` of the outer product Levi.
The condition on each `a i` is upper weak contraction: its forward normalized
absolute ratios are at most one. The inverse block scalar therefore supplies
the corresponding lower-radical contraction containment. These are weak
containments, with no strictness or eventual-contraction hypothesis.

Let `C(a) = Jacquet.compressedAction ρ hρ KP hKP (g a)`. This is precisely the
endomorphism of the actual `KP`-fixed vectors which applies `ρ (g a)` and then
the normalized `Compact.averageMap`. The tuple function `g` is only local
notation; the module introduces no new operator, quotient or group construction.

## Conclusions

The first clause asserts `C(a * b) = C(a) * C(b)` for all componentwise weakly
contracting `a` and `b`. Tuple multiplication is pointwise; endomorphism
multiplication is composition, applying `C(b)` first. Block scalars commute,
so the inverses defining `g` preserve this order.

The second clause says that for each such `a` and every actual `KP`-fixed
vector `v`,

```text
Jacquet.mk ρ N (C(a) v) = Jacquet.mk ρ N (ρ (g a) v).
```

Both sides belong to the actual coinvariant carrier, and `mk` is the existing
quotient map. Since `g a` lies in the refined Levi, the published `action_mk`
identifies the right side with its unnormalized descended action on `[v]`.
The displayed equality has no modulus, half-modulus or coset-index scalar.

The statement includes rank zero, empty products, one-block inner shapes,
zero representations and constant scalar tuples. There is no irreducibility,
finite length, tensor decomposition, canonical-lift certificate or condition
on the dimension of the whole carrier. At rank zero the product group is
trivial and the two identities reduce to identity-operator identities.
No stabilization, kernel equality, quotient surjectivity, admissibility or
generic comparison is asserted.

## Source and derived formulation

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019. The registered source is
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Relevant passages are the reductive-group setting on p.1, the quotient and
normalization in section 3 (pp.3–4), the factorization in section 4 (p.5), and
III.5.1–III.5.3 (pp.5–6). The original pp.1–7 and the formula images on pp.4–7
were read; no project errata file was found.

The provenance is derived. A finite product of the outer general linear groups
is a reductive group in that setting. The existing single-GL
`BlockCompressionStatement` records the analogous upper-radical laws and
`BlockCompressionProof` derives them through finite-orbit averages. The
present statement uses the opposite product radical and the actual product
compact open. The independent universes and block coordinates are internal
formal packaging.

Casselman's operator is an unnormalized finite coset sum, whereas the operator
here is a normalized average. His multiplicativity assertion III.5.3 is stated
in the strict chamber. Neither his operator nor that chamber is silently
identified with the present formulation. The weak version follows from the
explicit stronger containments in `HasBlockIwahoriFactorization`; the normalized
quotient formula follows because every relevant orbit summand has the same
quotient and the averaging coefficients sum to one.

Concretely, factor each `k i` in lower-Levi-upper order. The upper containment
and centrality of the scalar in the Levi imply that `ρ (g a) v` is fixed by
the product upper and compact Levi factors. Thus each of its `KP`-orbit values
is a translate by an element of the product lower intersection. Those lower
translations vanish in the actual coinvariant quotient, giving the second
clause. For the first clause, reduce the inner average to these lower translates
and use the lower contraction containment to absorb their conjugates into the
outer compact average. The published constant-orbit-value averaging lemma
formalizes both steps. This explanation describes the intended derivation;
the present module supplies only its proposition.

All averaging is over the genuine compact open `KP`. No openness of a radical
intersection in the ambient product group is assumed or needed.
