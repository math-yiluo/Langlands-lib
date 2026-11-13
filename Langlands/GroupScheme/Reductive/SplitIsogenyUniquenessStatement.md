# Unpinned uniqueness for isogenies of split reductive groups

Worker 3483.

`Langlands.GroupScheme.SplitIsogenyUniquenessStatement` is a `Prop`-valued
declaration of the uniqueness assertion for arbitrary isogenies of split
connected reductive groups over a field. This module states the proposition
and contains no proof.

## Source and translation

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Proposition 23.7, printed p.486 / one-based
PDF p.502, with the actual character-map convention of Proposition 23.5,
printed pp.485–486 / PDF pp.501–502. Proposition 23.7 says that two
isogenies inducing the same root-datum map differ by the inner
automorphism of a unique rational point of the target torus modulo its
centre. The complete retained official errata snapshot registered as
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction to
Propositions 23.5 or 23.7.

The declaration uses the actual restriction-map formulation of this
assertion. The weight map induced by an isogeny of the supplied pairs is
pullback on all characters of the target torus. Its equality is written as
`∀ χ : characterLattice T', t₁ ≫ χ = t₂ ≫ χ`. For the finite reduced root
systems of split connected reductive groups, the root correspondence and
characteristic-power factors are determined by this weight map. In the
split torus, characters also separate homomorphisms. Thus this condition
expresses the shared induced map in Proposition 23.7 without supplying
root indices, a base, or a pinning. It retains the central character
directions as well as the roots.

The proposition's conclusion uses the rational point of `T'/Z(G')`
specified in its statement. An intermediate lift notation in Milne's
proof does not impose rational-point lifting here. Categorical
composition below applies the first isogeny and then the inner
automorphism of the target, as in the proposition.

## Actual groups and hypotheses

All fields and schemes have an arbitrary universe `u`. The field `k` may
be imperfect and may have positive characteristic.

The actual group schemes `G` and `G'` are objects of
`Grp (Over (Spec k))`. The source has `IsConnectedReductive G`. The
target's connected reductivity is part of the supplied adjoint-quotient
interface below. Connected reductivity uses smoothness, affineness,
connectedness and trivial geometric unipotent radical.

The commutative group schemes `T` and `T'` have actual closed maximal
torus inclusions `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'`, expressed
by `IsMaximalTorus i` and `IsMaximalTorus i'`. The source torus is
explicitly split. Splitness of the target torus follows from the
supplied quotient-image interface. Maximality among all tori is required
for both inclusions.

The maps `φ₁ φ₂ : G ⟶ G'` are actual isogenies. The published predicate
`IsIsogeny` means that the underlying scheme morphism is finite, flat and
surjective. Neither isogeny is assumed central, separable, or an
isomorphism, and neither kernel is required to be smooth or reduced.
The maps `t₁ t₂ : T ⟶ T'` satisfy the two actual inclusion squares

`i ≫ φ₁ = groupHom t₁ ≫ i'`,

`i ≫ φ₂ = groupHom t₂ ≫ i'`.

They record the restrictions to the supplied tori. No separate
isogeny premise on these restrictions is needed: the ambient maps are
isogenies and both supplied tori are maximal.

The quotient data are `q : G' ⟶ A`, a commutative group scheme `T'_ad`,
`j : T'_ad.toGrp ⟶ A`, and `π : T' ⟶ T'_ad`, with
`h : IsAdjointSplitTorusImage q i' j π`. This published predicate
requires:

- An actual adjoint quotient `q` by the full scheme-theoretic centre,
  with its fppf and quotient universal properties.
- Actual maximal split tori `i'` and `j` in the original and adjoint groups.
- The square `groupHom π ≫ j = i' ≫ q`, with `π` flat, surjective and
  locally of finite presentation.

The published all-test theorem
`IsAdjointSplitTorusImage.comp_eq_one_iff_mem_center` identifies the kernel
of `π` with the preimage in `T'` of the full centre of `G'`. Thus `T'_ad`
is an actual representative of the torus quotient denoted `T'/Z(G')`
in the source. The interface keeps the entire scheme-theoretic preimage,
including any non-smooth part.

These quotient and image representatives are supplied with their intrinsic
laws. The declaration does not construct them. The published
`adjointSplitTorusImageExistenceStatement` supplies such torus-image data
for any supplied adjoint quotient and maximal split torus.

## Conclusion and scope

There is a unique actual ground-field point
`x : Over.mk (𝟙 (Spec k)) ⟶ T'_ad.toGrp.X` such that

`φ₁ ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom = φ₂`.

The published `innerAction` is the descended action of the actual adjoint
quotient on `G'`; `basePointIso` evaluates it at a ground-field point.
The equation is equality of actual group-scheme morphisms and therefore
controls every test scheme, including nonreduced tests. Uniqueness is for
the fixed quotient-image data and the fixed pair of isogenies.

The point is in the actual quotient torus, without any requirement that
it lift to `T'(k)` or `G'(k)`. The centre may have a torus part, so `π`
need not be finite. No smoothness, reducedness or connectedness condition
is imposed on the centre. The statement includes tori, empty root systems
and central torus factors.

This generalizes the map scope of the published
`SplitIsomorphismUniquenessStatement`, whose separate proof task remains
unchanged. It complements the existence and extension assertions in
`SplitIsogenyTheoremStatement` and the induced-map assertion in
`IsogenyRootDatumStatement`. This module proves none of these statements.
