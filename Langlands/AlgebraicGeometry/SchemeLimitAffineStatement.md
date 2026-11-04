# Relative affineness descent along affine scheme limits

The declaration
`Langlands.AlgebraicGeometry.AffineLimit.RelativeAffinenessDescent`
states the affineness clause of Conrad's Theorem 3.4(2) in a more general
scheme-limit formulation. The source is Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2) and its proof reference. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Let `D` be a small cofiltered diagram of affine schemes, with an actual
limit cone `c`. Its objects map compatibly to an affine scheme `S` by a
natural transformation `t`. A specified map `p : c.pt ⟶ S` agrees with
each limit projection followed by the corresponding structural map.
Let `a : X ⟶ S` and `b : Y ⟶ S`, and let `f : X ⟶ Y` satisfy
`f ≫ b = a`. Assume that `f` is quasi-compact and quasi-separated and
that `b` is quasi-compact.

The proposition says that the actual induced morphism

`c.pt ×[S] X ⟶ c.pt ×[S] Y`

is affine if and only if the corresponding morphism

`D.obj i ×[S] X ⟶ D.obj i ×[S] Y`

is affine for some index `i`. Both maps are the published
`AffineLimit.baseChangeMap`, constructed by the universal property of
the categorical pullback. The models `X` and `Y` can be nonaffine and
nonseparated. Diagram transitions need not be monomorphisms. The index,
its morphisms, and schemes share an arbitrary universe `u`.

This is a derived strengthening: local finite presentation is unnecessary
for this particular property. Conrad assumes both models finitely
presented over an affine coefficient ring. Those source assumptions imply
the hypotheses here: the models are quasi-compact and quasi-separated,
so `f` is quasi-compact and quasi-separated, and `b` is quasi-compact.
For a filtered diagram of coefficient rings, the opposite spectrum
diagram supplies the affine schemes and their limit, recovering the
affineness assertion after a coefficient stage has been chosen.

This unit states only relative affineness descent. It does not prove the
proposition or state the other properties in Theorem 3.4(2), initial
model existence, relative Hom comparison, or an arithmetic or topological
comparison.
