# Greatest unipotent closed subgroups under field isomorphisms and Galois transport

This module introduces a predicate for "closed unipotent subgroup containing
every unipotent closed subgroup" and proves that it is stable under ambient
isomorphisms and under base change along isomorphisms of fields. As a result,
such a subgroup of `G_K`, for `G` defined over `k`, is invariant under every
`σ ∈ Aut_k(K)`. This is the uniqueness argument in Milne's proof of
Theorem 16.6 ((a) ⇒ (b)): the subgroup `G_u` is unique, so it is stable under
the Galois group and descends to `k`.

Throughout, `k : Type u` is a field and group schemes are over
`Spec (CommRingCat.of k)`.

## Definition `IsGreatestUnipotentSubgroup`

For `i : U ⟶ G`, `IsGreatestUnipotentSubgroup i` is a structure with three
fields:

- `isClosedSubgroup : IsClosedSubgroup i`;
- `isUnipotent : IsUnipotent U`;
- `greatest`: for every group scheme `V` and every `j : V ⟶ G` with
  `IsClosedSubgroup j` and `IsUnipotent V`,
  `SubgroupFunctor.range j ≤ SubgroupFunctor.range i`.

So `i` is a closed unipotent subgroup that contains every closed unipotent
subgroup of `G`, on every test scheme. No smoothness or connectedness is
required. The Library's `IsUnipotentPart` and `IsUnipotentRadical` ask for
smooth connected subgroups, which does not fit Theorem 16.6, where `G_u` may
be neither.

**Provenance.** This predicate is internal. It packages the property that
Milne's Theorem 16.6 attributes to `G_u` ("G_u is unique and contains every
unipotent algebraic subgroup of G"), with algebraic subgroups represented by
closed subgroups (Milne, Proposition 1.41) and containment tested on points
over every test scheme, as in the published statement
`SeparablyTrigonalizableCriterionStatement`.

## Results

In the namespace `IsGreatestUnipotentSubgroup`:

- `range_eq`: if `i : U ⟶ G` and `j : V ⟶ G` both satisfy the predicate, then
  `range i = range j`. Each is a closed unipotent subgroup, so each range
  contains the other.
- `comp_iso`: if `i` satisfies the predicate and `e : G ≅ G'`, then so does
  `i ≫ e.hom`. Closedness transports by `IsClosedSubgroup.comp_iso`. For a
  closed unipotent `j : V ⟶ G'`, apply `greatest` to `j ≫ e.inv`, then push
  the inclusion forward along `e.hom` (`SubgroupFunctor.range_comp_mono`).
- `baseChange_ringEquiv`: if `[IsAffineHom G.X.hom]`, `i` satisfies the
  predicate and `f : k ≃+* K` is a ring isomorphism onto a field `K`, then
  `(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom f.toRingHom))).map i`
  satisfies the predicate over `K`. Write `b` for `Spec f` and `a` for
  `Spec f⁻¹`; then `a ≫ b = 𝟙` and both are isomorphisms. Closedness is
  `IsClosedSubgroup.baseChange`; unipotence is
  `RadicalFieldTransport.isUnipotent_map` (Milne 14.9). Given a closed
  unipotent `j : H ⟶ G_K`, its base change along `a`, composed with the
  canonical isomorphism `baseChangeSectionIso b a _ G : (G_K)_a ≅ G`, is a
  closed unipotent subgroup of `G`. So `greatest` bounds its range by
  `range i`, and `RadicalFieldTransport.range_le_of_section` turns this into
  `range j ≤ range (B.map i)`. The proof follows the Library proof of
  `IsUnipotentRadical.baseChange_ringEquiv`.

At the top level:

- `IsUnipotent.isGreatestUnipotentSubgroup`: let `[IsAffineHom G.X.hom]`,
  `IsClosedSubgroup i`, `IsUnipotent U`,
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
  `IsMultiplicativeType M` for `q : G ⟶ M`. Then
  `IsGreatestUnipotentSubgroup i`. The `greatest` field is
  `IsUnipotent.range_le_of_isFppfQuotient` from
  [`UnipotentKernelMaximal`](UnipotentKernelMaximal.md).
- `IsGreatestUnipotentSubgroup.range_radicalGaloisHom`: let `K` be a field
  extension of `k`, `G` over `k` with `[IsAffineHom G.X.hom]`, and
  `i : U ⟶ G_K` (base change along `algebraBaseMap k K`) satisfying the
  predicate. Then for every `σ : K ≃ₐ[k] K`,
  `SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i`.
  Here `radicalGaloisHom i σ` is the base change of `i` along `Spec σ`,
  composed with the canonical isomorphism `(G_K)_σ ≅ G_K`
  (`descentBaseChangeIso`). By `baseChange_ringEquiv` and `comp_iso` it
  satisfies the predicate, and `range_eq` concludes. This equality is
  exactly the hypothesis of the Galois descent theorem
  `Descent.GaloisInvariantClosedSubgroup.exists_descent`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Printed
page numbers; the one-based PDF page is the printed page plus 16.

- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." In the proof of
  (a) ⇒ (b), the subgroup over a Galois extension is unique, hence stable
  under the Galois group, hence defined over `k` (1.54).
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
