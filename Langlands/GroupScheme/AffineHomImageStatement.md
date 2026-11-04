# Fppf image factorization of homomorphisms of affine algebraic groups

`Langlands.GroupScheme.AffineHomImageStatement.{u}` is a Prop-valued
statement. This module supplies no proof.

## The assertion

For every field `k : Type u`, write `B` for `Spec (CommRingCat.of k)`. The
statement quantifies over actual group schemes `G H : GroupScheme B`, that is,
group objects in schemes over `B`. The hypotheses are exactly the four
instance arguments `LocallyOfFiniteType G.X.hom`, `IsAffineHom G.X.hom`,
`LocallyOfFiniteType H.X.hom` and `IsAffineHom H.X.hom`. It then quantifies
over every actual group homomorphism `f : G ⟶ H`.

The conclusion asserts that there exist an actual group scheme
`I : GroupScheme B` and actual homomorphisms `q : G ⟶ I` and `i : I ⟶ H`
with the following properties:

- `LocallyOfFiniteType I.X.hom` and `IsAffineHom I.X.hom`: the
  intermediate group is affine and locally of finite type over `k`;
- `IsClosedSubgroup i`: the underlying scheme morphism of `i` is a closed
  immersion;
- `q ≫ i = f`: in diagrammatic order, `f` is `q` followed by `i`;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q`.

The last condition is the Library's existing represented fppf quotient
predicate. It says that the underlying scheme morphism of `q` is flat,
surjective and locally of finite presentation. It also says that
`SubgroupFunctor.range (kernelι q)` equals `SubgroupFunctor.range (kernelι f)`.
Here `kernelι` is the inclusion of the actual scheme-theoretic kernel, the
pullback along the unit section. Both ranges are subgroup functors of `G`
evaluated on every test scheme `T` over `B`. By the published
`mem_range_kernelι_iff`, the equality says: for every such `T`, a point
`x : T ⟶ G.X` is killed by `q` exactly when it is killed by `f`. Surjectivity
refers to the underlying scheme map. The predicate does not assert that
`q` is surjective on the `T`-points for any fixed test scheme `T` or field.
This matches Milne's example after Definition 5.5: for `n ≠ 0` the `n`th
power map of `Gm` is a quotient map, although it need not be surjective on
`R`-points.

The universe `u` is arbitrary. The statement has no smoothness,
connectedness, reducedness, perfect-field or characteristic premise. It does
not assume a previously constructed image or quotient: the group `I` and both
homomorphisms are part of the asserted existence.

## Source and translation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field*, corrected reprint, Cambridge University Press,
2022. Registered source: `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
Printed page `p` is zero-based PDF page index `p + 10`.

- Definitions 1.1 and 1.2 (printed pp. 6–7): an algebraic group over `k` is
  a group object in the category of schemes of finite type over `k`. It is
  an affine algebraic group when its scheme is affine. A homomorphism is a
  morphism of schemes compatible with multiplication.
- Theorem 3.34 (printed p. 75), the homomorphism theorem for affine groups:
  every homomorphism `φ : G → H` of affine algebraic groups factors as
  `G → I → H` with `G → I` faithfully flat and `I → H` a closed immersion.
- Theorem 5.39 (printed p. 108) gives the same factorization for all
  algebraic groups. Its proof takes `N = Ker(φ)` and the quotient map
  `G → G/N`. Theorem 5.13 (printed p. 101) factors `φ` through this
  quotient. The induced monomorphism `G/N → H` is a closed immersion by
  Theorem 5.34.
- Definition 5.5 (printed p. 99) defines a quotient map as a faithfully
  flat homomorphism. Remark 5.40 (printed p. 108) states that the
  factorization is essentially unique. Remark 5.42 calls `I` the image of
  `φ`.
- Propositions 5.43, 5.45 and 5.46 (printed pp. 109–110) give the sheaf
  interpretation. A homomorphism `G → Q` with kernel `N` is the quotient of
  `G` by `N` exactly when `R ↦ G(R)/N(R)` is a fat subfunctor of `Q`. For
  the image `I`, `G → I` is a quotient map, and `I(R)` consists of the
  points of `H(R)` that lift to `G(R')` for some faithfully flat
  `R`-algebra `R'`.

The official errata for the 2022 reprint
(`https://jmilne.org/math/Books/iagerrata2022.html`, read 2026-11-03) were
checked. Their only entry among these results corrects a typographical slip
in Remark 5.40: its second `q` should be `q'`. This does not affect
Theorems 3.34, 5.13 or 5.39.

The translation is as follows. Over `B`, `IsAffineHom G.X.hom` makes the
scheme `G.X.left` affine, hence quasi-compact. Together with
`LocallyOfFiniteType G.X.hom`, this makes `G` of finite type over `k`. So
the hypotheses say exactly that `G` and `H` are affine algebraic groups in
Milne's sense. Morphisms in `GroupScheme B` are his homomorphisms. Milne's
`φ = i ∘ q` is the Lean equation `q ≫ i = f`.

The finite-type affine setting gives each displayed property of the
factorization:

- `I` is a closed subgroup scheme of the affine finite-type group `H`. A
  closed immersion is affine and of finite type. Hence `I` is affine and
  locally of finite type over `k`, and `i` is a closed subgroup inclusion.
- Faithful flatness of `q` means that its underlying scheme morphism is flat
  and surjective.
- The composite of `q` with the structure map of `I` is the structure map of
  `G`, which is locally of finite type. Hence `q` is locally of finite type.
  Its target `I` is of finite type over a field, hence locally noetherian. A
  morphism locally of finite type into a locally noetherian scheme is
  locally of finite presentation.
- The closed immersion `i` is a monomorphism and preserves the unit. Hence,
  on every test scheme, a point is killed by `q` exactly when it is killed by
  `q ≫ i = f`. So the actual kernel of `q` has the same all-test range as the
  actual kernel `N = Ker(f)`. This matches Milne's identification of
  `G → I` with the quotient `G → G/N`.

Thus the factorization supplies the full `RelativeRoot.IsFppfQuotient`
conclusion. This fppf cover with prescribed kernel is the represented form
of the sheaf quotient in Propositions 5.45 and 5.46. Milne's functors of
points are evaluated on `k`-algebras `R`, that is, on the affine test
schemes `Spec R`. The Lean kernel ranges are compared on all test schemes
over `B`, which include these.

## Provenance and relation to the Library

This statement is a direct formalization of the affine case of Milne's
homomorphism theorem. It is published as a prerequisite for the actual
diagonal-kernel geometry task `d1fee1c3-e435-49e7-a1d4-8b431470d790` and the
structural splitting statement task `4fe37606-9ed8-4910-a71b-9e0e8ae0a63f`.
Those arguments need images of homomorphisms between affine algebraic group
schemes that may be nonsmooth and disconnected.

The Library's `AffineHomImage` module constructs the schematic image group
of a homomorphism between affine group schemes over a field.
`AffineHomImage.isFppfQuotient` proves the fppf quotient property of its
projection only for a smooth source. The `Rational.SplitTorusImage` module
treats diagonalizable sources, and the `Adjoint.SplitTorusImageStatement`
module concerns maximal split tori in adjoint quotients. None of these states the present
generic theorem, which has no smoothness premise.
