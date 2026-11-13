# Unpinned uniqueness in the split Isomorphism Theorem

Worker 3483.

`Langlands.GroupScheme.SplitIsomorphismUniquenessStatement` is a
`Prop`-valued declaration of the uniqueness clause for isomorphisms of split
connected reductive groups over an arbitrary field. This module states the
proposition and contains no proof.

## Source and translation

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Proposition 23.7, printed p.486 / PDF p.502,
and Theorem 23.25 and Remark 23.26, printed pp.492–493 / PDF pp.508–509.
Proposition 23.7 says that two isogenies inducing the same map on root
data differ by the inner automorphism of a unique rational point of the
target torus modulo the target centre. Theorem 23.25 and Remark 23.26
include the isomorphism case. The full official errata snapshot registered
as `milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
these statements.

The declaration uses the restriction-map form of the isomorphism case.
For isomorphisms carrying the supplied maximal tori onto one another,
the weight map on root data is pullback on their actual characters.
Equality of these weight maps is therefore written directly as equality
of character pullback. No root indexing, base, or pinning is needed in
this formulation. It asserts neither that an isomorphism induces a root
datum equivalence nor existence of a lift of an arbitrary root datum
equivalence; those are separate parts of the Isomorphism Theorem.

## Objects and hypotheses

All schemes and fields have an arbitrary universe `u`. The field `k` is
unrestricted: it may be imperfect or have positive characteristic.

The source and target are actual group schemes `G` and `G'` over `Spec k`,
using `GroupScheme = Grp (Over (Spec k))`. The source has
`IsConnectedReductive G`. The target's connected reductivity is supplied
by the adjoint-quotient interface described below. These predicates use
smoothness, affineness, connectedness and trivial geometric unipotent
radical; they do not assume classification.

The commutative group schemes `T`, `T'` have inclusions
`i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'`. The hypotheses
`IsMaximalTorus i` and `IsMaximalTorus i'` refer to actual closed maximal
tori. `T` is explicitly split. Splitness of `T'` is part of the supplied
image interface, so both pairs are split reductive groups. Merely being
maximal among split tori is insufficient here: the statement explicitly
requires maximality among all tori.

The quotient data consist of an actual homomorphism `q : G' ⟶ A`, a
commutative group scheme `T'_ad`, an inclusion `j : T'_ad.toGrp ⟶ A`,
and `π : T' ⟶ T'_ad`, satisfying the published predicate
`IsAdjointSplitTorusImage q i' j π`:

- `q` is an actual adjoint quotient by the full scheme-theoretic centre,
  with its fppf and quotient universal properties.
- `T'` and `T'_ad` are maximal split tori in their respective groups.
- `groupHom π ≫ j = i' ≫ q`, and `π` is flat, surjective and locally
  of finite presentation.

This expresses the genuine scheme-level quotient image of `T'` in `A`.
The imported all-test theorem
`IsAdjointSplitTorusImage.comp_eq_one_iff_mem_center` identifies the
kernel of `π` with the preimage in `T'` of the full centre of `G'`.
Thus `T'_ad` represents the torus quotient denoted `T'/Z(G')` in the
source. The notation presupposes the usual containment of the centre in
the maximal torus; the interface retains the entire scheme-theoretic
preimage without a smoothness condition.

These are supplied actual quotient and image representatives, with their
intrinsic laws, rather than a rational-point lifting assumption. Their
existence is a separate structural result; the published
`adjointSplitTorusImageExistenceStatement` constructs such image data
for any supplied adjoint quotient and maximal split torus. This
declaration does not construct an adjoint quotient or an image.

Finally, `φ₁ φ₂ : G ≅ G'` are actual isomorphisms, and
`t₁ t₂ : T ≅ T'` are actual torus isomorphisms satisfying the two
inclusion squares. For every actual character
`χ : characterLattice T' = Hom(T', G_m)`, they satisfy
`t₁.hom ≫ χ = t₂.hom ≫ χ`. This retains the full character lattice,
including central torus directions. Character separation for a split
torus shows why this is the same restriction condition; its proof is not
part of the present statement module.

## Conclusion and boundaries

There is a unique actual base point
`x : Over.mk (𝟙 (Spec k)) ⟶ T'_ad.toGrp.X` whose image in `A` acts on
`G'` by an inner automorphism making

`φ₁ ≪≫ innerAction.basePointIso (x ≫ j.hom.hom) = φ₂`.

Categorical composition applies `φ₁` first and then this automorphism of
the target. `IsAdjointQuotient.innerAction` is the descended scheme action
of the adjoint quotient on `G'`; `basePointIso` evaluates it at a ground
field point. The equation is equality of actual group-scheme
isomorphisms, so it controls all test schemes, including nonreduced ones.
The uniqueness concerns `x` for the fixed quotient-image data and the
fixed pair of isomorphisms.

The point need not lift to a `k`-point of `T'` or of `G'`. No
surjectivity of `T'(k) → T'_ad(k)` is assumed or asserted. The quotient map
need not be finite, since the centre may contain a torus. Neither the
centre nor the kernel is required to be reduced, smooth, or connected.
The statement includes groups that are tori, empty root systems, and
central torus factors. It supplies no noncentral-isogeny theorem or
uniqueness theorem for isogenies that are not isomorphisms.

The published `SplitIsomorphismTheoremStatement` and
`splitIsomorphismTheorem` provide the complementary existence clause.
The present declaration records the unpinned uniqueness clause at the
actual rational quotient-torus scope, independently of their proof.
