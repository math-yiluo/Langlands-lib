/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.CanonicalCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import WeilConjectures.AlgebraicGeometry.InternalScalarNormalizationExistence
import WeilConjectures.AlgebraicGeometry.SectionPullNormalizationTransport
import WeilConjectures.AlgebraicGeometry.SectionTensorNormalizationTransport

/-! # Normalized internal scalar extension and geometric pullback

Source: Stacks Tags 03EK, 06YY, 0G7E and 07A6.
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

/-- Scalar extension is restricted derived tensor and commutes with geometric pullback,
with the universal computation normalizations and the fixed section comparisons.

(1),
scalar-refined reduction comparison; Stacks Tags 03EK, 06YS, 06YY, 0G7E, 0D6D,
07A6 and 0B65 (auxiliary; not a blueprint node).

Proof (the eight steps of the node):
1. Use lem-pe-internal-section-tensor-comparison,
lem-sfb-internal-section-scalar-adjunction, and the section derived pushpull and tensor
normalizations to transport the actual operations and their universal computation maps.
2. The ordinary extension/tensor comparison followed by symmetry sends s tensor x to
x tensor s. Balancing gives its inverse. The single degree-zero total comparison has
only the (n,0) summand, with no sign.
3. On a flat-term K-flat P, compose the restricted scalar computation counit, the
localized ordinary comparison, and the inverse tensor localization map. The counit is
invertible by lem-pur-derived-change-of-rings; the tensor map is invertible with just
one K-flat factor by lem-sf-ringed-derived-native-tensor. Descend through
lem-weil-pbc-site-derived-tensor-descent.
4. For an arbitrary complex A choose a flat-term K-flat resolution P to A using
lem-pc-kflat-resolution. Naturality and cancellation of the derived image of this
quasi-isomorphism prove TensorNormalized at A; tensoring the resolution need not be
invertible.
5. Naturality of the coefficient isomorphism pulled from the point makes the ring-map
square commute. The internal inverse-image comparison and
lem-sfb-kflat-scalar-comparison-normalization identify its balanced map on generators.
6. The ordinary map is the inverse of the specified pullIso: its transpose is
comapLowerStarIso, since units insert 1 and counits multiply. Uniqueness in
situation-conventions identifies this particular conjugate.
7. Ringed pullback preserves flat-term K-flat complexes, including coefficient change
without flatness. Descend the balanced comparison and use step 6. Naturality and
cancellation as in step 4 give PullNormalized on all homotopy complexes.
8. The fixed scalar and geometric section comparisons preserve the actual derived
Hom transposes, units and counits. Their representative squares give the section-ring
K-flat formulas for both normalized maps. Descent proves naturality and independence
of representatives. Identity maps, zero target rings, nonflat quotients, unbounded
complexes and empty schemes are all included. -/
theorem internal_scalar_pullback_normalization (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
      (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
      (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y),
      TensorNormalized a X tX ∧ TensorNormalized a Y tY ∧ PullNormalized a f b ∧
      SectionScalarNormalized a X sX ∧ SectionScalarNormalized a Y sY ∧
      SectionTensorNormalized a X sX tX ∧ SectionTensorNormalized a Y sY tY ∧
      SectionPullNormalized a f sX sY b := by
  let tX := canonicalCoefficientTensorNormalization a X
  let tY := canonicalCoefficientTensorNormalization a Y
  have htX := (canonicalCoefficientTensorNormalization_normalized a).1 X
  have htY := (canonicalCoefficientTensorNormalization_normalized a).1 Y
  obtain ⟨b, hb⟩ := internal_pull_normalization_exists a f
  obtain ⟨sX, hsX⟩ := internal_section_scalar_normalization_exists a X
  obtain ⟨sY, hsY⟩ := internal_section_scalar_normalization_exists a Y
  exact ⟨tX, tY, b, sX, sY, htX, htY, hb, hsX, hsY,
    section_tensor_normalized_of_normalized a X sX hsX tX htX,
    section_tensor_normalized_of_normalized a Y sY hsY tY htY,
    section_pull_normalized_of_normalized a f sX sY hsX hsY b hb⟩

end AlgebraicGeometry.ProEtale.QuotientChange
