# Existence and independence of parabolic root presentations

This pair states three structural obligations and their conjunction
`Langlands.GroupScheme.ParabolicRootPresentationStatement`. It provides no
proof. It uses the actual presentation construction in
`GroupScheme/Rational/ParabolicRootPresentation` and introduces no replacement
group, root datum or cone.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.9, printed p.112/PDF p.118, supplies reduction to a standard parabolic.
V.3.14, printed p.113/PDF p.119, chooses a minimal parabolic contained in a
specified `P = MN`, with its maximal split torus containing the specified
split component of `M`, and restricts the complementary simple roots.
V.3.15 on the same page defines the strictly positive and nonnegative
root-combination cones. VII.2.1, printed p.227/PDF p.233, later requires a
cone condition for every parabolic.

These statements make the existence and choice issues in that presentation
explicit. They are derived structural comparison targets, rather than
additional verbatim numbered theorems in the source. Their arbitrary-field
scope explicitly generalizes the source's local-field setting. The underlying
predicates are the common framework's rational parabolic, rational Levi and
split-component predicates. Nonreduced relative roots, arbitrary
characteristic, nonsplit ambient groups and rank zero are retained.

`ParabolicRootPresentationExistenceStatement` quantifies over a field, a
connected reductive group `G`, actual maps `p : P → G` and `l : M → P`,
and an actual map `a : A → M` from a commutative group scheme. From
`IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`, and `IsSplitComponent a`,
it asserts `Nonempty (ParabolicRootPresentation p l a)`. In particular, the
specified maps are fixed before the presentation is sought. This is stronger
than producing a presentation of an unspecified conjugate parabolic or an
unspecified Levi.

The presentation's published definition requires actual maximal split-torus
data, a generic cocharacter, a simple-root subset, and a factorization of the
specified component map. Its correctness predicate also retains equality
of the supplied parabolic and Levi images with the standard subgroup
functors on every test scheme, the compatible dynamic minimal parabolic
contained in the supplied parabolic, and a single standard cocharacter
realizing both images. Thus the existence conclusion includes actual
nonempty choice data; an empty family of standard cocharacters cannot
satisfy it.

`ParabolicRootPresentationIndependenceStatement` fixes the actual maps
`p`, `l`, and `a` and quantifies over **any** two compatible presentations
`r` and `s`. It asserts equality of their restricted root sets, strictly
positive root-combination cones and nonnegative root-combination cones.
No maximal split torus, torus embedding, generic cocharacter, minimal
parabolic, simple-root subset or component factor is fixed between `r`
and `s`. These equalities concern subsets of the same full real character
space `RealTorusSpace.Vstar A`. They do not merely compare two factorizations
through one fixed torus.

`ParabolicRootPresentationIsoStatement` additionally allows two commutative
group schemes `A` and `A'` with specified component maps `a` and `a'`. It
takes an actual isomorphism `e : A ≅ A'` and requires
`groupHom e.hom ≫ a' = a`. For every presentation `r` of `p,l,a` and every
presentation `s` of `p,l,a'`, it asserts equality of the images of their
restricted root sets and both cones under real character pullback in
both directions. Pullback along `e.hom : A → A'` sends the sets for `A'`
to those for `A`; pullback along `e.inv` gives the reverse equalities.
Every root-presentation choice may vary here as well.

Connected reductivity supplies the affine instance. For the cone statements,
its smoothness supplies local finite type, so the presentation's existing
split-torus Lie-weight finiteness theorem supplies the finite simple-root
set needed by the cone definitions. No separate root-system realization,
finite-root premise or characteristic restriction is added. Both cone
definitions remain in the full character space, including central
directions: they are sums of restricted roots with respectively positive
or nonnegative coefficients. They are not chambers defined by coroot
inequalities. The empty complementary-root set has cone `{0}`.

The aggregate is exactly the conjunction of those three universally quantified
propositions. The independence propositions alone do not imply existence:
their universal quantification over presentations could otherwise be
vacuous. The separate existence assertion is therefore a required part of
the aggregate and of any use claiming coverage of every parabolic.

No proof of these targets, comparison with Renard's simple indivisible-root
convention, central-direction decomposition, or representation-theoretic
temperedness assertion is supplied. The separate
`RenardRootConventionStatement` compares the implemented simple roots to
the source convention. This pair concerns the presentation choices after
the root constructions have been fixed. Structural proofs and accepted
publication remain necessary before reporting these assertions as theorems.
