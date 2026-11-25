/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteExtension
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteClosure

/-! # Scalar extension of a diagonal diagram

Source: diagonal tower coefficient changes, paragraphs (1)--(2).
(blueprint: lem-diagonal-coefficient-family-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Extend a Z_l diagonal diagram to the integral, rational and closure
coefficient stages, with the specified scalar/direct-image mates. This result
requires neither a chosen Cartier class nor a completed reference.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (1)--(2).
(blueprint: lem-diagonal-coefficient-family-extension).

Proof: For each finite extension, use finite freeness over Z_l to identify
extension of scalars with a finite biproduct. This identifies the unit and
root-line endpoints by their adjoints. Additive right-derived direct images
preserve finite biproducts, making the canonical scalar mates invertible on
the two specified lines. Transport the diagonal arrow, the three traces and
the supported sources through these comparisons; naturality carries each
integration composite to the image of its original identity. Rationalization
is localization at l. The unit and shifted line objects have common lower
bound -2, and the projective-line projections are qcqs. Bounded continuity
therefore makes the localization/direct-image mates invertible on these
objects. Apply the same transport. The closure coefficient and its root line
are the filtered finite-field colimits. Bounded continuity supplies the same
comparisons for those colimits. Their normalized adjoints determine the maps
on each finite-field leg, so scalar-extension associativity gives the rational
transition and closure squares. All constructions preserve the input Z_l
component literally; no choice of a new diagonal class is made. -/
theorem diagonalCoefficientFamily_extension
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)) :
    ∃ family : Family l Y, family.zl = d := by
  classical
  have hfinite := fun E : PadicAlgCl.FiniteIntermediateField l ↦
    diagonalCoefficient_finiteExtension l Y hY d E
  choose integral rational hIntegral hRational using hfinite
  let toIntegral := fun E ↦ (hIntegral E).some
  let toRational := fun E ↦ (hRational E).some
  obtain ⟨closure, hClosure, hTransitions⟩ :=
    diagonalCoefficient_finiteClosure l Y hY d integral rational toIntegral toRational
  exact ⟨{
    zl := d
    integral := integral
    rational := rational
    closure := closure
    toIntegral := toIntegral
    toRational := toRational
    toClosure := fun E ↦ (hClosure E).some
    rationalTransitions := fun E F h ↦ (hTransitions E F h).some }, rfl⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
