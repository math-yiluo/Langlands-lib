# Rational points of torsors over finite fields

`Langlands.GroupScheme.FiniteFieldTorsorPointStatement` states the following
consequence of Lang's theorem, at arbitrary universe `u`. Let `k : Type u` be
a finite field and `H` a smooth connected affine group scheme over `Spec k`.
If a scheme `X` over `Spec k` carries an actual left `H` action, its structure
map is flat, surjective, and quasi-compact, and the shear morphism

`H × X → X × X`, `(h, x) ↦ (h • x, x)`,

is an isomorphism, then `X` has a `k`-rational point.

The action is the existing Mathlib `ModObj H.X X` in the cartesian monoidal
category `Over (Spec k)`. Its unit and multiplication laws are part of that
structure. The shear is the existing `ModObj.leftSMul H.X X`, and its
isomorphism condition concerns the actual relative scheme map. The other
three conditions on `X.hom` say that it is an fpqc cover. The conclusion uses
the published `RingPoint k X k` type of actual relative scheme morphisms.
There is no supplied rational point, orbit representative, or cohomology
vanishing premise.

These hypotheses describe a left torsor by intrinsic maps. They translate the
right-torsor convention of Milne, *Algebraic Groups* (2017), Definition 2.66,
printed page 59 (PDF page 75), by replacing a left action with the right
action `x • h = h⁻¹ • x`. Proposition 2.69, printed page 60, descends
smoothness and affineness to torsors; the fpqc formulation here uses the
usual faithfully flat descent of those properties. Smoothness and affineness
over a field in particular give finite type. Proposition 2.72, printed
page 61, identifies torsors with their nonabelian first cohomology classes,
and Corollary 17.98, printed page 383 (PDF page 399), says this cohomology is
trivial for a connected group over a finite field. A trivial torsor has a
rational point. These results give the asserted consequence.

The registered Milne errata snapshot dated 2026-11-02 corrects the torsor
discussion on page 60 to allow nonaffine bases. This statement retains an
arbitrary actual scheme `X` and has the affine base `Spec k`, so it does not
assume the conclusion of affine descent. No correction in that snapshot
changes the finite-field Lang consequence. This module records a derived
proposition and supplies no proof.
