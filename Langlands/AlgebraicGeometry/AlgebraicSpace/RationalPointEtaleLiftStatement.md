# Lifting rational points of quasi-separated algebraic spaces to étale charts

Author: Worker 105.

This module states the lifting input that Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), uses in the proof of
Proposition 5.4. The cited result is Knutson II.6.4. The module only states it and
contains no proof.

## Statements

Fix a field `k : Type u` and an actual algebraic space
`X : AlgebraicSpace (Spec (CommRingCat.of k))`, as defined in
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`: an fppf sheaf on schemes
over `Spec k` with representable diagonal and a surjective étale scheme atlas.

- `RationalPointEtaleLift k X` says that for every
  `x : RingPoints k X k` (a `k`-point of `X`, that is, a section of `X` over the
  actual `Spec k` with identity structure map), the following data exist:
  - an actual scheme `U : Over (Spec (CommRingCat.of k))` whose underlying scheme
    `U.left` is affine;
  - a morphism of algebraic spaces `f : (schemeToSpace _).obj U ⟶ X` from the
    space associated to `U`, whose underlying transformation `hom f` is étale in the
    Library sense `AlgebraicSpace.IsEtale` (representable, with every represented
    base change étale);
  - a relative scheme point `u : RingPoint k U k`, that is, a morphism
    `Spec k ⟶ U` over `Spec k`, whose image
    `RingPoints.map f ((schemeRingPointsEquiv k U k).symm u)` is `x`.
- `RationalPointEtaleLiftStatement` says that `RationalPointEtaleLift k X` holds
  for every field `k : Type u` and every algebraic space `X` over `Spec k` that
  satisfies `IsQuasiSeparated X` (from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`).

## Sources

Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 15, the first sentence of the proof of Proposition 5.4: "The
uniqueness holds due to the requirement on étale maps and the fact that for every
x ∈ X(k) there exists an étale map U → X from a scheme U admitting a point
u ∈ U(k) such that u ↦ x [Kn, II, Thm. 6.4]." Conrad's Proposition 5.4 (printed
p.14) concerns "a (quasi-separated) algebraic space locally of finite type over k"
for a henselian valued field `k`.

Knutson's book is not a registered source here. The formal statement follows the
Stacks Project, registered source `stacks-decent-spaces-chapter-ed88ff78-2026-11-05`
(chapter "Decent Algebraic Spaces", version ed88ff78; registered folder
fingerprint `878f5241b88f6791dc4c96ee48fc36c3e2e3e54852b029d7662bf6d432e7c4c8`,
chapter PDF SHA-256
`2e29935b33d7a90b4fcdfa1ce801af37406a0f0dc6d9103d54ffd2263122a3e6`):

- the implication diagram after Definition 6.1 (Tag 03I8): a quasi-separated
  algebraic space is decent;
- Lemma 11.4 (Tag 0BBP): "Let S be a scheme. Let X be a decent algebraic space over
  S. For every point x ∈ |X| there exists an étale morphism (U, u) → (X, x) where U
  is an affine scheme, u is the only point of U lying over x, and the induced
  homomorphism κ(x) → κ(u) is an isomorphism";
- Lemma 11.1 (Tag 03K4), Definition 11.2 (Tag 0EMW) and the paragraph after it:
  on a decent space each point is represented by a monomorphism
  `Spec κ(x) → X`, and any morphism from the spectrum of a field in the class of
  that point factors through it.

## Relation to the sources and derived content

Conrad's sentence asks only for some scheme `U`. The requirement that `U.left` be
affine comes from Stacks Lemma 11.4 and is stronger. It is included because the
rest of Conrad's proof uses separated étale schemes and étale maps from schemes
of finite type over `k`, and an affine scheme étale over a locally finite type
space is both. The statement does not keep the other conclusions of Lemma 11.4
(that `u` is the only point over `x`, and the residue field isomorphism).

The rational-point form is derived from the Stacks results as follows. Let
`x : Spec k → X` be a `k`-point and let `x` also denote its image in `|X|`.
Then `x` factors through the monomorphism `Spec κ(x) → X`. Take `(U, u)` as in
Lemma 11.4. The isomorphism `κ(x) ≅ κ(u)` gives
`Spec k → Spec κ(x) ≅ Spec κ(u) → U`, which is a `k`-point of `U` over `x`. All
morphisms here are morphisms over the base `Spec k`.

The quasi-separatedness hypothesis matches Conrad's convention for Section 5
(printed p.13): "We will work with quasi-separated algebraic spaces (as is the
case throughout [Kn])". The statement assumes no finiteness
condition on `X` and no condition on `k` beyond being a field, matching Knutson's
and Stacks' generality rather than Conrad's henselian locally finite type setting.

Also derived here: the names, the use of `RingPoints k X k` for `X(k)`, and the
formulation of "u ↦ x" through `RingPoints.map` and
`schemeRingPointsEquiv`.
