# Quotients of smooth affine groups by normal closed subgroups: statement

Worker 1379.

`NormalSubgroupQuotientStatement.{u}` concerns a field `k : Type u`, a
smooth affine group scheme `G` over `Spec k`, and a homomorphism
`i : N ⟶ G` of group schemes over `Spec k` with `IsClosedSubgroup i`
(the underlying morphism of schemes is a closed immersion) whose range
subgroup functor `SubgroupFunctor.range i` is normal (`IsNormal`, that
is, stable under conjugation by all points of `G` on every test scheme).
It asserts that there are a group scheme `Q` over `Spec k` and a
homomorphism `q : G ⟶ Q` such that

- `Q` is smooth and affine over `Spec k`, and
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` holds: the
  morphism of schemes underlying `q` is flat, surjective and locally of
  finite presentation, and the range of the published scheme-theoretic
  kernel `kernelι q` is exactly `SubgroupFunctor.range i` on every test
  scheme.

`N` itself is not assumed smooth.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`:

- Theorem 5.14, printed p.102 (one-based PDF p.118): "Every normal
  algebraic subgroup N of an algebraic group G arises as the kernel of a
  quotient map G → Q."
- Proposition 5.18, printed p.103 (one-based PDF p.119): "Every normal
  algebraic subgroup N of an affine algebraic group G is the kernel of a
  quotient map G → Q with Q affine."
- Corollary 5.26, printed p.105 (one-based PDF p.121): "If G is smooth, so
  also is G/H."

In Milne a quotient map is a faithfully flat homomorphism of algebraic
groups (Definition 5.5, printed p.99). Over a field, a homomorphism of
algebraic groups is of finite presentation, so a faithfully flat one is
flat, surjective and locally of finite presentation. The kernel of a
quotient map is the scheme-theoretic kernel, which is what
`SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i` records on
points. An algebraic subgroup of `G` in Milne is a closed subgroup
scheme, here a closed immersion `i`; a smooth affine group scheme over a
field is of finite type, hence an algebraic group in Milne's sense.

The statement specializes the source to smooth affine `G` and combines
the three results: 5.14 gives the quotient, 5.18 makes it affine and 5.26
makes it smooth. It does not assert the universal property of the
quotient or its uniqueness.

This file only defines a proposition and proves nothing. It is a premise
of `CentralMaximalTorusBaseChangeReductionStatement`.
