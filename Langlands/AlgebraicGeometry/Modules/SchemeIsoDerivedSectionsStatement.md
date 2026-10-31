# Actual derived sections under a scheme isomorphism

`Langlands.AlgebraicGeometry.Modules.SchemeIsoDerivedSectionsStatement.{u}`
is an internal transport statement for the universal-perfect-sections
development. This file defines the proposition and supplies no proof.

For any `R : CommRingCat.{u}`, schemes `X Y : Scheme.{u}`, scheme
isomorphism `e : X ≅ Y` and structure morphism `g : Y ⟶ Spec R`, it
asserts a natural isomorphism between the following functors on
`Y.Modules`:

- Pull back along `e.hom`, take the actual derived relative sections over
  `e.hom ≫ g`, and include the result in the unbounded derived category.
- Take the actual derived relative sections over `g` and include the
  result in the same category.

Actual derived relative sections are exactly
`DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections ...)`,
with the published functors and Mathlib's standard derived category.
The natural isomorphism is asserted by `Nonempty`. Its component at `M`
identifies the derived sections of `e^* M` with those of `M`; naturality
is with respect to every actual module morphism on `Y`.
There is no quasi-coherence, flatness, properness or noetherianity
hypothesis.

The provenance is an internal consequence of existing Library results:
`SchemeIsoCohomology` supplies `pushforwardEquivalence`;
`ClosedImmersionHigherDirectImageVanishingProof` gives vanishing of
positive higher direct images along an isomorphism; and
`DerivedPushforwardComparison` gives the actual derived comparison and
its coefficient naturality. The pullback–pushforward adjunction unit is
invertible because pushforward is an equivalence. These facts motivate
the statement rather than introduce another cohomology theory.

This statement concerns transport along scheme isomorphisms over a
fixed affine base. It asserts neither a perfect representative nor
geometric scalar base change, and does not identify a Čech complex with
derived sections.
