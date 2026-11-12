# Descent of a valuative lift along a dominating extension

Author: Worker 1543.

`SpaceValuativeExtensionDescentStatement` is the extension-removal
assertion of Stacks Project, *Morphisms of Algebraic Spaces*,
Lemma 67.41.4 (Tag 0ARH), printed pp. 85–86. The module defines
the proposition and supplies no proof.

The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, retained folder
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms of
Algebraic Spaces, full chapter PDFs (version ed88ff78)/`, folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`.
The cited file is `spaces-morphisms.pdf`, SHA-256
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.
The extension diagrams are those of Definition 67.41.1 (Tag 03IX),
printed pp. 82–83.

## Exact statement

Let `S` be any scheme, let `X` and `Y` be algebraic spaces over `S`,
and let `f : X ⟶ Y` satisfy `IsSeparatedMorphism f`. Let `A` be any
valuation ring with fraction field `K`, and let `s : Spec A → S`.
Given sections `x : X(K)` and `y : Y(A)` whose images in `Y(K)`
agree, assume `HasDominatingValuativeLift f A K s x y`.

The supplied lift predicate means that there are a valuation ring `B`
with fraction field `L`, compatible maps `A → B` and `K → L` with
`A → B` local, and a section of `X(B)` restricting to `x|_L` and mapping
to `y|_B`. The conclusion supplies `a : X(A)` with `a|_K = x` and
`f(a) = y`. All pullbacks are the actual algebraic-space section
pullbacks in `Over S`. Rings and fields lie in universe `u`.

This statement has no quasi-compactness, finite type, universal closedness,
noetherian or decency hypothesis. No restriction is imposed on the field
extension allowed by the premise. Only existence of a section with the
two original triangle equations is asserted; there is no additional
assertion about its equality with the supplied section over `B`.

## Source route and purpose

Lemma 67.41.4 first reduces to `Y = Spec A` and then forms the
scheme-theoretic image of the supplied section `Spec B → X`.
It proves that this image is `Spec A` by an affine étale chart,
torsion freeness over the valuation ring and descent of étaleness.
This describes the source argument and is not an implemented Lean proof.

For Task 5368 this statement removes the extension supplied by
`SpaceValuativeExtensionExistenceStatement`. Their composition has the
exact conclusion of the unchanged `SpaceValuativeExistenceStatement`.
