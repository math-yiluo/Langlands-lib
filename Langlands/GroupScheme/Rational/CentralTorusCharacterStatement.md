# Central tori detect nonzero rational characters

Author: Worker 1110.

The universe-polymorphic proposition
`Langlands.GroupScheme.CentralTorusCharacterStatement` says that, over every
field `k`, every nonzero rational character `χ ∈ X^*(G)_k` of a connected
reductive group `G` restricts to a nonzero character of some central closed
subtorus `i : Z ⟶ G`, where `Z` is a commutative group scheme that is affine and
locally of finite type over `k`.
This module defines the proposition as a `Prop`-valued `def`; it supplies no proof.

## Hypotheses

The universe `u` is arbitrary. The proposition quantifies over every
`k : Type u` with a `Field k` instance and every
`G : GroupScheme (Spec (CommRingCat.of k))`. A group scheme here is the published
group object in schemes over `Spec k`, with its multiplication, unit and inverse.
There is no perfectness, characteristic, splitness, local-field or
algebraic-closedness hypothesis on `k` or `G`.

The hypothesis `IsConnectedReductive G` has exactly its published meaning in
[`Reductive.Basic`](../Reductive/Basic.md): the structure morphism of `G` is
smooth and affine, the underlying scheme of `G` is connected, and the base change
of `G` to `AlgebraicClosure k` has trivial unipotent radical. The last condition,
`HasTrivialUnipotentRadical`, says that every closed subgroup `H` of that base
change which is smooth, connected, unipotent and normal has trivial range as a
subgroup functor. This is the geometric condition; triviality of only the
`k`-unipotent radical would be the weaker pseudo-reductive condition and is not
the hypothesis here.

The character `χ : rationalCharacters G` is the published notion from
[`Rational.Characters`](Characters.md): a homomorphism of group schemes over `k`
from `G` to the multiplicative group `𝔾_m`, written in the additive group
`X^*(G)_k`. Addition is pointwise multiplication of character values, so the
hypothesis `χ ≠ 0` says that `χ` is not the constant identity character. This is
nontriviality as a group-scheme morphism, not a condition solely on the values
of `χ` on `G(k)`. If `G` has no nonzero rational character, the implication from
`χ ≠ 0` is vacuous, and such groups remain within the quantified scope.

## Conclusion

The conclusion asserts the existence of a commutative group scheme
`Z : CommGroupScheme (Spec (CommRingCat.of k))` and a homomorphism of group
schemes `i : Z.toGrp ⟶ G` from its underlying group scheme `Z.toGrp`, satisfying
six conditions.

- `IsAffineHom Z.toGrp.X.hom` says that the structure morphism `Z ⟶ Spec k` is
  affine, so the underlying scheme of `Z` is affine.
- `LocallyOfFiniteType Z.toGrp.X.hom` says that this structure morphism is
  locally of finite type. Together with the affine conjunct, the coordinate ring
  of `Z` is a finitely generated `k`-algebra, as for an algebraic group in
  Milne's sense. Both conjuncts are stated explicitly, rather than left to be
  deduced from the torus condition by descent, because the torus lemma that
  consumes this statement requires them.
- `IsTorus Z.toGrp` has its published meaning in
  [`Torus.Lattice`](../Torus/Lattice.md): there exist a field `K : Type u` (at
  the same universe `u` as `k`) and a `k`-algebra structure on `K` such that the
  base change of `Z.toGrp` along `Spec K ⟶ Spec k` is a split torus, meaning
  isomorphic over `K` to a finite product of copies of `𝔾_m`. This follows
  Milne's Definition 12.14. The torus is not required to be split over `k`.
- `IsClosedSubgroup i` has its published meaning in
  [`Reductive.Basic`](../Reductive/Basic.md): the underlying morphism of schemes
  of `i` is a closed immersion. Thus `Z` is a closed subgroup of `G`.
- `IsCentral i` has its published meaning in
  [`Rational.Characters`](Characters.md): for every test scheme `T` over
  `Spec k`, every point `x : T ⟶ Z` maps under `i` into the published subgroup
  functor `center G` at `T`. A point `g` of `G(T)` lies in that centre when, for
  every morphism `T' ⟶ T` of test schemes, the restriction of `g` to `T'`
  commutes with every point of `G(T')`. This is functorial centrality, stronger
  than checking only the centre of `G(k)`. It does not presuppose that a
  representing centre of `G` exists or is smooth or reduced, which matters in
  positive characteristic.
- `characterRestrict i χ ≠ 0`: the published `characterRestrict i` is
  precomposition with `i`, sending `χ` to the character `χ ∘ i` of `Z.toGrp`.
  The conjunct requires this group-scheme character of `Z` to be nontrivial.

The torus `Z` and its inclusion `i` are existential and may depend on `χ`. The
proposition does not assert that one torus detects all characters, nor that `Z`
is split, maximal, or the radical of `G`. It assumes no split component, no
factorization, and no derived-group statement.

## Sources and derived provenance

The proposition is derived; neither source below states it. The sources state
the structure facts from which it follows.

- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field* (2017), source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  - Proposition 21.61, printed p.443 / PDF p.459, holds over an arbitrary field,
    which need not be perfect. Its implication (b)⇒(c) notes that the radical
    `R(G)` is a torus and applies the same argument as in the proof of
    Proposition 21.60.
  - Proposition 21.60, implication (b)⇒(c), printed p.442 / PDF p.458, takes
    `S = R(G)`, a central torus with `G/S` semisimple. Then `G/S` is perfect by
    Corollary 21.50 (printed p.440 / PDF p.456), and Proposition 12.46 shows
    that `G` is the almost-product of `S` and its derived group.
  - Proposition 12.46(b), printed p.245 / PDF p.261, states that for a central
    torus `T` of `G` with `G/T` perfect, the multiplication map `T × DG → G` is
    surjective. Central subgroups are defined in Definition 12.44 on the same
    page.
  - Corollary 6.19(d), printed p.129 / PDF p.145, states that every
    homomorphism from `G` to a commutative algebraic group is trivial on `DG`.
  - Definition 12.14, printed p.236 / PDF p.252, defines a torus as an algebraic
    group that becomes isomorphic to a finite product of copies of `𝔾_m` over
    some field containing `k`; this is the convention of `IsTorus`.
  - The definition of a reductive group recalled on printed p.400 / PDF p.416
    (smooth connected, with trivial geometric unipotent radical) matches
    `IsConnectedReductive`.
- Milne's official *Errata for Algebraic Groups (2017)*, retained HTML snapshot
  of 2 November 2026, source ID
  `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
  The complete page was checked; no entry corrects any passage cited above.
  - Chapter 21 has entries for p.440 (the proof of Theorem 21.51 was
    rewritten), p.445 (Theorem 21.68(d)), p.447 (the proof of Proposition
    21.71), p.449 (a proof that appealed to 21.67), pp.456–460 (the examples of
    types `A_n`, `C_n`, `D_n`, including 21.96–21.99) and p.461 (Exercise
    21-2). Theorem 21.51 enters 21.60 only through the implication (c)⇒(d),
    which the argument above does not use. The other entries concern results
    and examples that the argument does not use. None corrects 21.50, 21.60 or
    21.61.
  - Chapter 12 has entries for p.244 (in 12.41 a subgroup should be central)
    and p.249 (a missing step in the proof of 12.57). Neither result is used in
    the proof of 12.46, and there is no entry for 12.14, 12.44 or 12.46.
  - The displayed Chapter 6 entry concerns Example 6.48 on p.136. The HTML
    source also carries a comment, not displayed on the page, that in
    6.19(c,d,e) `G` should be assumed smooth; here `G` is smooth.
  - The Chapter 19 entry for p.399 concerns Definition 19.7 (almost-simple
    groups); there is no entry for the definition recalled on p.400.
- David Renard, *Représentations des groupes réductifs p-adiques*, French
  edition dated 9 July 2026, source ID
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
  Section V.2.1, printed p.104 / PDF p.110, recalls that `R(G)` is a central
  torus, that `G` is generated by `R(G)` and `DG`, and that their intersection
  is finite. Section V.2.2, printed p.105 / PDF p.111, recalls that rational
  characters are trivial on `DG`. Renard works over a nonarchimedean local field
  `F`, so the arbitrary-field scope of the proposition comes from Milne.

The derivation motivating the statement is as follows. A rational character `χ`
of `G` is a homomorphism to the commutative group `𝔾_m`, so it is trivial on
`DG` (6.19(d)). If `χ` were trivial on the central torus `R(G)`, it would be
trivial on the image of `R(G) × DG → G`, which is all of `G` (12.46(b) via the
proof of 21.60 and 21.61). Hence a nonzero `χ` restricts nontrivially to
`R(G)`, which is a central closed subtorus of `G`, affine and of finite type
over `k`. This paragraph explains the derived provenance; its argument has not
been implemented as a Lean proof in this statement module.
