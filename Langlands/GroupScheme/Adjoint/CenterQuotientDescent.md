# Trivial centre of a full-centre quotient from the second-centre property

Module `Langlands.GroupScheme.Adjoint.CenterQuotientDescent`, namespace
`Langlands.GroupScheme.CenterQuotientCenter`. Throughout, `G Q : GroupScheme S`
are group schemes over an arbitrary base scheme `S` and `q : G ⟶ Q` is a
homomorphism.

## Declarations

- `comm_mem_center_of_comp_mem_center`: assume the actual kernel of `q` is the
  centre of `G`, that is `SubgroupFunctor.range (kernelι q) = center G`. Let
  `g : T ⟶ G.X` be a point whose image `g ≫ q` is central in `Q`. Then for every
  `a : T' ⟶ T` and every `h : T' ⟶ G.X`, the commutator
  `(a ≫ g) * h * (a ≫ g)⁻¹ * h⁻¹` lies in `center G` over `T'`.
- `comp_eq_one_of_mem_center`: under the same kernel hypothesis, a central point
  of `G` is killed by `q`.
- `center_eq_bot_of_secondCenterTrivial`: if
  `RelativeRoot.IsFppfQuotient (center G) q` holds and `G` has trivial second
  centre (`SecondCenterTrivial G`, module
  `Langlands.GroupScheme.Adjoint.SecondCenter`), then `center Q = ⊥`.
- `centerQuotientCenterTrivial_of_secondCenterTrivial`: if every connected
  reductive group over a field has trivial second centre, then
  `CenterQuotientCenterTrivialStatement.{u}` holds. The hypotheses
  `IsAffineHom Q.X.hom` and `LocallyOfFiniteType Q.X.hom` of that statement are
  not used.

## Proof

*Commutators.* Since `g ≫ q` is central, `a ≫ g ≫ q` commutes with `h ≫ q`.
Composition with `q` preserves products and inverses, so the commutator of
`a ≫ g` and `h` maps to `1`. The Library lemma
`CenterQuotientDescent.mem_center_of_comp_eq_one` (module
`Langlands.GroupScheme.Adjoint.QuotientDescent`) then puts the commutator in
`center G`.

*Central points are killed.* Rewrite `center G` as the range of `kernelι q`. A
point in that range is the image of a kernel point, and
`kernelPointsEquiv q T` says that point maps to `1`.

*Main theorem.* `IsFppfQuotient (center G) q` says that `q.hom.hom.left` is
flat, surjective and locally of finite presentation, and that the kernel of `q`
is `center G`. Let `z : T ⟶ Q.X` be a central point. The pullback
`p₀ : T ×_{Q} G ⟶ T` of `q.hom.hom.left` along `z.left` is again flat,
surjective and locally of finite presentation, because these properties are
stable under base change. The second projection is a point `g` of `G` over
`T' := T ×_{Q} G` with `g ≫ q = p ≫ z`, where `p : T' ⟶ T` is `p₀` viewed as a
morphism over `S`. The point `p ≫ z` is central, since the centre is a
subgroup functor and so is stable under restriction. By the commutator lemma,
every commutator of a restriction of `g` lies in `center G`. Trivial second
centre then makes `g` central, so `g ≫ q = 1`, which gives `p ≫ z = p ≫ 1`.
A flat, surjective morphism locally of finite presentation is an epimorphism
of schemes, and `Over.epi_of_epi_left` makes `p` an epimorphism in `Over S`.
Cancelling `p` gives `z = 1`.

*Statement-level corollary.* Apply the main theorem to the given `q` and the
group `G`, which is connected reductive.

## Provenance

This is the descent half of the proof of Milne, *Algebraic Groups* (2017),
Corollary 17.62(e): the quotient of a connected reductive group by its centre
has trivial centre. Milne takes the inverse image `Z'` of the centre of
`G/Z(G)` in `G`, shows by Corollary 12.41 (applied with `H = Z'` and
`N = Z(G)`) that `G` acts trivially on `Z'` by conjugation,
and concludes `Z' = Z(G)`. Here the inverse image is not formed. Instead a
central point of the quotient is lifted along the fppf cover given by the
quotient map, and the equation `z = 1` is descended by cancelling an
epimorphism. The group-theoretic half (a connected reductive group has trivial
second centre, which replaces Milne's use of 12.41) is not part of this module.
