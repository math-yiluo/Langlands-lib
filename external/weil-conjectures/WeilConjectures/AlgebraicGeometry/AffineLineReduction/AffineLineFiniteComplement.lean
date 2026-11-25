/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
/-!
# A finite complement in the affine-line model

Source: latest blueprint, sk-thm-wft-affine-curve-upper.proof.md, paragraphs 1-2
(blueprint: lem-a1-affine-line-finite-complement).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.AffineLineReduction

/-- A dominant affine-line open has a finite closed complement over the base field.

Source: latest blueprint, sk-thm-wft-affine-curve-upper.proof.md, first paragraph
and second paragraph's finite complement Z
(blueprint: lem-a1-affine-line-finite-complement).

Proof: the affine line is smooth of relative dimension one. Apply the existing
source theorem for the finite reduced complement of a dense open in a smooth
curve. Its output is a reduced finite scheme Z with a closed immersion over the
base and exactly the desired image. The over-morphism identity identifies the
composite structural map in this statement with the finite structural map in
that theorem. The empty complement is included. No coefficients are used. -/
theorem exists_finite_closed_complement (K : Type u) [Field K] {U : Scheme.{u}}
    (j : U ⟶ affineLine K) [IsOpenImmersion j] [IsDominant j] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ affineLine K),
      IsClosedImmersion i ∧ IsFinite (i ≫ affineLine K ↘ Spec (.of K)) ∧
      Set.range i = (Set.range j)ᶜ := by
  have : SmoothOfRelativeDimension 1 (affineLine K ↘ Spec (.of K)) := by
    have h := AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of K))
    simpa only [Nat.card_unique] using h
  obtain ⟨Z, hZ, i, hi, hiOver, hfin, hred, hij⟩ :=
    exists_isReduced_isClosedImmersion_range_eq_compl_of_curve (k₀ := K) j
  let := hZ
  let := hiOver
  refine ⟨Z, i, hi, ?_, hij⟩
  rw [comp_over i (Spec (.of K))]
  exact hfin

end AlgebraicGeometry.AffineLineReduction
