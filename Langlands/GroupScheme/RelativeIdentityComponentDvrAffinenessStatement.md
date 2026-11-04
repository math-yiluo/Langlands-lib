# Affineness of the relative identity component over a DVR

`Langlands.GroupScheme.RelativeIdentityComponent.SmoothDvrAffinenessStatement`
is the following proposition in an arbitrary universe `u`. For every
commutative integral domain `R : Type u` with `IsDiscreteValuationRing R`,
every actual group scheme `G` over `Spec R` whose structural morphism is smooth
and affine, and every actual homomorphism `i : H → G` satisfying
`IsRelativeIdentityComponent G i`, the structural morphism of `H` is affine.

## Exact objects and hypotheses

The base is the actual affine scheme `Spec (CommRingCat.of R)`. Mathlib's
`IsDiscreteValuationRing R` says that the domain `R` is a local principal ideal
ring with nonzero maximal ideal. In particular a field is excluded by this
convention. All group schemes and test schemes share the arbitrary universe `u`.

The supplied `i` is a homomorphism in the existing `Grp(Over (Spec R))`
architecture. Its representation hypothesis says that its underlying map is an
open immersion and, for every test scheme `T` over `Spec R`, a point
`x : T → G` factors through `i` precisely when the image in every actual residue
fibre lies in the connected component of the identity. This quantifies over
nonreduced and nonaffine test schemes as well. It is the published
`IsRelativeIdentityComponent` predicate without alteration.

Affineness in both the premise and conclusion is `IsAffineHom` of the actual
structural morphism. Since the base is affine, it is equivalent to affineness of
the corresponding total scheme. The proposition imposes no henselianity,
perfection of the residue field, connectedness of the generic fibre, or choice
of a uniformizer. Smoothness and affineness of `G` are explicit premises.

## Source and correspondence

Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive group schemes*, with an
appendix by Brian Conrad, §3.5, unnumbered lemma and proof, author-preprint
PDF pp. 6–7; the arbitrary-DVR convention is on PDF p. 5. Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
The retained copy has 34 pages and different pagination from the published
J. Algebraic Geom. 15 (2006), 507–549 version.

The lemma states that the neutral component of a smooth affine group scheme
over the DVR is smooth affine. Here the neutral component is identified by the
published all-test representation predicate, so the declaration asserts the
affineness part for every actual representative. The source's opening of §3.5
identifies the component as the union of the generic and special neutral
components, and cites SGA 3 VI_B §3 for that definition. The existing predicate
implements the fibre-image criterion of that section.

The source first obtains affineness using its Proposition 3.1 and also cites
Bruhat–Tits II, Corollaire 2.2.5(iii). Its alternative dilatation description uses
connectedness of the generic fibre. That extra hypothesis belongs to the
alternative description and is absent from the affineness lemma. The stricter
base assumption in §3.6 likewise belongs to the later Chevalley-scheme section.
The source was read through the end of the §3.5 proof. No separate errata note
for this registered source was present in the current Library or project notes
when checked.

## Scope

This file declares a proposition and contains no proof of it. Existence,
smoothness, geometric connectedness, normality, and compatibility with arbitrary
base change belong to the separate smooth relative-component targets.
Affineness over a DVR can be stated using only the published representation
predicate, without importing those pending statements. Its proof remains a
separate obligation. The declaration introduces no integral model, dilatation,
parahoric, smoothening, or descent construction.
