# Exhaustive normalized-cocycle presentation of actual deformations

Module `Langlands.AlgebraicGeometry.Picard.DualNumberDeformationPresentation`,
namespace `Langlands.AlgebraicGeometry.Picard.DualNumberThickening`.

Fix a field `k : Type u`, a scheme `X : Scheme.{u}`, and a morphism
`f : X ⟶ Spec k`. The thickening, projection and zero section are the actual
scheme pullback and morphisms defined in `DualNumberThickening`. Fix a family
`T : ι → X.Opens`, where `ι : Type u`.

The main result `exists_cocycle_presentation` says that if `T` covers `X` and
each `T i` is affine, then every actual line bundle `L` on `thickening f`
with a specified actual zero-section trivialization

```lean
e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X
```

admits an additive structure-sheaf cocycle `z` on `T` and an isomorphism

```lean
L.obj ≅ CocycleGluing.glued (unitCochain f T z).
```

Here `unitCochain` consists of the actual units `1 + epsilon*z` on the
inverse images of pairwise intersections. The additive cocycle predicate
is `CechDegreeOne.IsCocycle (G := structureSheaf X) T z` from the existing
module-sheaf Cech construction. Neither separatedness nor quasi-compactness
is required for this presentation result; the cover is prescribed in advance.

## Construction and implemented proof

`coefficientUnit_unitCoefficient_of_reduction_eq_one` proves that an actual
unit reducing to one equals the coefficient unit of its extracted coefficient.
The existing coefficient map first divides a unit by the projection lift of
its reduction. Under the stated hypothesis this normalization leaves the unit
unchanged, and the unit-kernel equivalence and its inverse cancel.

For a module sheaf `M` on the thickening, a zero-section trivialization `e`,
and sections `s i` over `thickenedOpens f T i`, assume the sections have
reduced coefficient one. If `g` gives their transitions in the convention
`s j = g i j • s i` on each overlap, then
`unitReduction_eq_one_of_normalized_transition` proves that every `g i j`
reduces to one. Apply `reducedCoefficient` to the transition equation. Its
scalar formula multiplies by the actual reduction of `g i j`; its restriction
formula restricts the two reduced coefficients. Both coefficients restrict
to one, so the reduction of the transition is one.

When the `s i` are actual local frames,
`frameCoefficientCochain f T M s hs` extracts the coefficient of their actual
transition units `CocycleGluing.frameCocycle s hs`.
`unitCochain_frameCoefficientCochain` identifies the resulting coefficient
units with those original transition units. This uses their reduction to one
and the preceding recovery formula.

`isCocycle_frameCoefficientCochain` now follows from the cocycle identity for
frame transitions and the proved equivalence between actual unit cocycles
and additive structure-sheaf cocycles in `DualNumberCocycles`.
`normalizedFrameIso` applies the actual frame-reconstruction isomorphism
`CocycleGluing.frameIso`, using the identified transitions and the fact that
the inverse images of a cover still cover the thickening. For this step,
`M` may be any module sheaf carrying the stated frames and trivialization;
no separate line-bundle hypothesis is needed.

Finally, `exists_cocycle_presentation` takes the normalized frame on each
prescribed affine open from `DualNumberAffineFrames.affineNormalizedFrame`
(in the present namespace). The three preceding constructions supply its
cocycle, cocycle identity and actual module-sheaf isomorphism.

## Independence of presentations

`isCoboundary_of_presentations` considers any two additive cocycles `z,w`
and isomorphisms from one module sheaf `M` to their glued sheaves. Composing
one inverse with the other gives an isomorphism between the two glued
sheaves. The previously proved `nonempty_iso_unitCochain_iff` therefore
shows

```lean
CechDegreeOne.IsCoboundary (G := structureSheaf X) T
  (fun i j ↦ w i j - z i j).
```

The sign agrees with the convention `d(b) i j = b j| - b i|`. This result
needs no cover or affineness assumption and places no compatibility condition
on the two presentation isomorphisms. Consequently it also applies to
presentations obtained from different reduction trivializations or frames.

## Provenance and scope

This is an internal construction combining actual affine normalized frames,
the actual unit-kernel coefficient map, frame reconstruction, and the
additive-coboundary classification already implemented in the imported
modules. Every comparison used in the proof is one of those constructions
or a lemma proved here. No new external source assertion is introduced.

The result concerns actual module-sheaf presentations and their additive
coboundary independence. It does not yet identify deformation classes with
derived cohomology, supply the rigidification comparison, or prove the
linearity or final tangent-to-H1 comparison of the host task.
