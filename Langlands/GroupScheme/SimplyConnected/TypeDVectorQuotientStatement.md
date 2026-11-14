# The vector quotient of a simply connected group of type `D_n`

Author: Worker 349.

`Langlands.GroupScheme.TypeDVectorQuotientStatement.{u}` is an **unproved** statement. It says
that a simply connected group of type `D_n` (`n ≥ 4`) whose star action fixes the vertex
numbered `0` maps by a central isogeny onto a form of the split special orthogonal group
`SO_{2n}`, with kernel killed by the fundamental weight at vertex `0`. There is no
characteristic hypothesis.

## Hypotheses

- `K : Type u` is a field and `G` is an affine, locally finite type group scheme over
  `Spec K` with an actual index `d : TitsIndexData G`;
- `e : d.Vertex ≃ Fin n` with `4 ≤ n`, and `d.cartan a b = CartanMatrix.D n (e a) (e b)` for
  all vertices `a, b`. In Mathlib's numbering of `CartanMatrix.D n` the vertices
  `0, 1, …, n − 3` form a chain and `n − 3` is joined to both `n − 2` and `n − 1`; vertex `0`
  is the end of the long arm;
- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- for every `γ : K^s ≃ₐ[K] K^s` (`K^s = SeparableClosure K`) and every vertex `a` with
  `(e a).val = 0`, `d.star γ a = a`.

These are the hypotheses of `ClassicalTypeDAlignedSpinCoverStatement`, except that the star
condition is stated only at the vertex numbered `0` instead of at all vertices `a` with
`(e a).val + 2 < n`. The two conditions are equivalent for every `n ≥ 4`, because the star
action is by automorphisms of the based root datum, hence by automorphisms of the Dynkin
diagram:

- for `n ≥ 5`, every diagram automorphism of `D_n` fixes each vertex `0, 1, …, n − 3` of the
  long arm, so both conditions hold automatically;
- for `n = 4`, the target condition asks that vertices `0` and `1` be fixed. Vertex `1` is
  the unique trivalent vertex of Mathlib's `CartanMatrix.D 4` (edges `0–1`, `1–2`, `1–3`), so
  every diagram automorphism fixes it, and the target condition reduces to the condition at
  vertex `0` stated here. It selects vertex `0` among the three end vertices `0, 2, 3`, which
  triality permutes.

The vertex-`0` form is the one the argument below uses.

## Conclusion

There exist a group scheme `H` over `Spec K`, affine and locally of finite type, and a
morphism `p : G ⟶ H` such that

- `IsCentralIsogeny p`;
- `(GroupScheme.baseChange (algebraBaseMap K K^s)).obj H` is isomorphic to
  `identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K^s))`, the split
  `SO⁰_{2n}` of the hyperbolic quadratic form on `K^s^(Fin n ⊕ Fin n)` (see
  `OrthogonalMatrix/Basic.md`);
- for every vertex `v` with `(e v).val = 0`, `d.FundamentalWeightTrivialOnKernel v p`: the
  fundamental weight at vertex `0` is trivial on `ker p ∩ T` over `K^s`, read through all
  `K^s`-scheme points (see `SpinCoverFundamentalWeight.md`).

## Mathematical content

The expected proof, not carried out in Lean:

1. Over `K^s` the group `G` is split, with the pinning recorded by `d`, and its root datum
   is simply connected of type `D_n`; so `G_{K^s} ≅ Spin_{2n}`. The centre `Z` of `G` is
   finite of multiplicative type, with character group `X*(Z_{K^s}) = P/Q` (weight lattice
   modulo root lattice, `Z/4` for `n` odd and `(Z/2)²` for `n` even).
2. Let `ϖ₀` be the fundamental weight at vertex `0`, the highest weight of the vector
   representation of `Spin_{2n}` when vertex `0` is chosen as the vector vertex (for `n ≥ 5`
   it is the only possible choice). Its class in `P/Q` has order 2, and its kernel
   `μ ⊂ Z_{K^s}` is the kernel `μ₂` of the vector representation `Spin_{2n} → SO_{2n}`; so
   `G_{K^s}/μ ≅ SO⁰_{2n}` (KMRT §27.B, type `D_n`: the vector representation factors through
   `O⁺`).
3. The Galois group acts on `X*(Z_{K^s}) = P/Q` through the star action on the diagram.
   Since the star action fixes vertex `0`, it fixes the class of `ϖ₀`, so `μ` is
   Galois-stable and descends to a central `K`-subgroup `μ_K` of `G`.
4. `H = G/μ_K` (the Library's quotient of a group by a finite central subgroup) with the
   quotient map `p` is a central isogeny, `H_{K^s} ≅ G_{K^s}/μ ≅ SO⁰_{2n}`, and
   `ker p ∩ T = μ` is killed by `ϖ₀`.

For `n ≥ 5` the alignment is automatic: the three order-2 subgroups of the centre of
`Spin_{2n}` (for `n` even) give `SO_{2n}` and two half-spin groups, and the half-spin groups
are not isomorphic to `SO_{2n}`. For `n = 4` triality permutes the three end vertices, and the
star condition at vertex `0` is what makes the vector quotient defined over `K`.

## Provenance

This is a **derived** statement. Tits 1968, §3, Remarque 3 (printed p.31 / PDF p.14,
registered source `tits-1968-formes-quadratiques-clifford`, PDF SHA-256
`f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782`) states that every
connected `k`-group of type `D_m`, `m ≠ 4`, is isomorphic to a form `H` of `SO⁰_{2m}`, to its
universal cover `H̃` or to its adjoint group; for simply connected `G` this gives the central
isogeny `G ≅ H̃ → H`. The vector character is described in KMRT (*The Book of Involutions*,
1998), §27.B, type `D_n`, printed p.379 / PDF p.402 (registered source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, PDF SHA-256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`). The case `n = 4` with
the star condition at vertex `0`, and the alignment with the Library's
`FundamentalWeightTrivialOnKernel`, are the derived argument above; they are not quoted from
the sources.

## Use

Together with `Quaternionic.EvenSpecialOrthogonalFormStatement` it implies
`ClassicalTypeDAlignedSpinCoverStatement`: identify `H ≅ O(q)⁰` by Tits's theorem and take
`π = p ≫ (H ≅ O(q)⁰) ≫ (O(q)⁰ ⟶ O(q))`. The inclusion `O(q)⁰ ⟶ O(q)` is a closed immersion, so
composing with it does not change the kernel and preserves the alignment.
