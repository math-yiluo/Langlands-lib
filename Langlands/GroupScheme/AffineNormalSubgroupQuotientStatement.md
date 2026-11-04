# Quotients of affine algebraic groups by normal closed subgroups: statement

Worker 1519.

`AffineNormalSubgroupQuotientStatement.{u}` concerns a field `k : Type u`,
a group scheme `G` over `Spec k` whose structure morphism `G.X.hom` is
locally of finite type and affine, and a homomorphism `i : N ⟶ G` of group
schemes over `Spec k` such that

- `IsClosedSubgroup i`: the morphism of schemes underlying `i` is a closed
  immersion, and
- `(SubgroupFunctor.range i).IsNormal`: for every scheme `T` over `Spec k`,
  the `T`-points of `G` that factor through `i` are stable under
  conjugation by all `T`-points of `G`.

It asserts that there are a group scheme `Q` over `Spec k` and a
homomorphism `q : G ⟶ Q` such that

- the structure morphism `Q.X.hom` is locally of finite type and affine,
  and
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` holds: the
  morphism of schemes underlying `q` is flat, surjective and locally of
  finite presentation, and the range of the actual scheme-theoretic kernel
  inclusion `kernelι q` equals `SubgroupFunctor.range i` on every test
  scheme over `Spec k`.

No smoothness, connectedness or reducedness is assumed of `G` or `N`, and
nothing is asserted about smoothness of `Q`. There is no separate
finiteness hypothesis on `N`: its structure morphism is the composite of
the closed immersion `i` with that of `G`, so it is locally of finite type
and affine as well.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field*, corrected reprint, Cambridge University Press, 2022, source
ID `milne-2022-algebraic-groups` (PDF SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`).
Printed page `p` is zero-based PDF index `p + 10`.

- Theorem 5.14, printed p.102 (index 112): "Every normal algebraic subgroup
  N of an algebraic group G arises as the kernel of a quotient map G → Q."
- Proposition 5.18, printed p.103 (index 113): "Every normal algebraic
  subgroup N of an affine algebraic group G is the kernel of a quotient map
  G → Q with Q affine." Milne remarks after its proof that this proves
  Theorem 5.14 for affine `G`.
- Definition 5.5, printed p.99 (index 109): a homomorphism of algebraic
  groups is a quotient map if it is faithfully flat, that is, flat and
  surjective.
- Theorem 5.13, printed p.101 (index 111): every homomorphism from `G`
  whose kernel contains the kernel `N` of a quotient map `q` factors
  uniquely through `q`. Milne deduces that a quotient map is determined by
  its kernel up to unique isomorphism and writes it `G → G/N`.

The author's errata page for the 2022 reprint
(https://jmilne.org/math/Books/iagerrata2022.html, read 2026-11-03) has no
entry for pp.99–103 or for the definitions used below.

## Translation

- *Algebraic group.* Milne's algebraic group is a group object in schemes
  of finite type over `k` (p.6, Definition 1.1). Here `G` is affine over
  the affine scheme `Spec k`, hence quasi-compact, so locally of finite type
  is the same as finite type; `G` is exactly an affine algebraic group in
  Milne's sense. The same holds for `Q`.
- *Algebraic subgroup.* Milne's algebraic subgroup is an algebraic group
  that is a subscheme of `G` with homomorphic inclusion (Definition 1.3,
  p.7), and every algebraic subgroup is closed (Proposition 1.41, p.19).
  Here it is given by a homomorphism `i` whose underlying morphism is a
  closed immersion, which identifies `N` with a closed subgroup scheme of
  `G`.
- *Normality.* Milne's condition is that `N(R)` is normal in `G(R)` for all
  `k`-algebras `R` (Definition 1.51(a), p.21). The Lean condition asks this
  on all schemes `T` over `Spec k`, which contains Milne's condition on the
  affine tests `Spec R`. Conversely, as `G` and `N` are affine, Milne's
  condition applied to the coordinate ring of `G ×ₖ N` makes the
  conjugation morphism `G ×ₖ N → G` factor through `N`, and that gives the
  condition on every `T`.
- *Quotient map.* Milne's quotient map is flat and surjective. Since `G`
  and `Q` are of finite type over `k`, the morphism `q` is locally of finite
  type over the locally Noetherian scheme `Q`, hence locally of finite
  presentation. So "faithfully flat" is equivalent here to the three
  geometric conditions in `IsFppfQuotient`, which is why the represented
  fppf formulation is used.
- *Kernel.* Milne's kernel is the fibre product `G ×_Q e` of `q` with the
  unit section (Section 1e, p.23), the closed subscheme whose `R`-points
  are the kernel of `G(R) → Q(R)`. The Library's `kernelι q` is the
  inclusion of this pullback. "`N` is the kernel of `q`" is recorded as the
  equality of the point subgroup functors
  `SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i` on every
  test scheme.

The statement is the affine case of Theorem 5.14, which is Proposition
5.18 together with the finite-type conclusion on `Q` contained in Milne's
notion of algebraic group. Non-affine algebraic groups are not covered.
It does not assert the universal property of Theorem 5.13, uniqueness of
`Q`, smoothness of `Q`, or surjectivity of `q` on the points of each test
scheme.

## Relation to other Library statements

`NormalSubgroupQuotientStatement` is the smooth specialization: it assumes
`G` smooth and also concludes that `Q` is smooth (Milne, Corollary 5.26).
The present statement drops smoothness of `G`, which is needed to form
quotients by successive normal closed subgroups whose intermediate
quotients need not be smooth, as in the inductive proof of Milne,
Theorem 16.26, printed p.332 (index 342). It is not a formal
generalization of the smooth statement, since it does not conclude
smoothness of `Q`.

This file only defines a proposition and proves nothing.
