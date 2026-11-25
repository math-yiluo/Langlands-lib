/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.OverlapLaurentCoordinates
import WeilConjectures.AlgebraicGeometry.AffinePuncturedLine.AffinePuncturedLineAlgebra

/-! # Normalizing an overlap unit by a change of chart frame

## References

* Stacks Project, Tag 0BXJ, proof
* Stacks Project, Tag 0BXJ, proof, Laurent-unit
  computation and removal of the constant boundary, for n=1
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

/-- A unit on the overlap is a standard transition unit after rescaling the first frame. -/
theorem exists_normalized_overlap_unit (k : Type u) [Field k]
    (v : Γ(ProjectiveLine (Spec (.of k)),
      standardOpen _ (Spec (.of k)) (⟨0⟩ : ULift.{u} (Fin 2)) ⊓
        standardOpen _ (Spec (.of k)) (⟨1⟩ : ULift.{u} (Fin 2)))ˣ) :
    ∃ (d : ℤ)
      (a : Γ(ProjectiveLine (Spec (.of k)),
        standardOpen _ (Spec (.of k)) (⟨0⟩ : ULift.{u} (Fin 2)))ˣ),
      Units.map ((ProjectiveLine (Spec (.of k))).presheaf.map
        (homOfLE inf_le_left).op).hom.toMonoidHom a * v =
          transitionUnit (ULift.{u} (Fin 2)) (Spec (.of k)) d ⟨0⟩ ⟨1⟩ := by
  let S := Spec (.of k)
  let U₀ := standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩
  let U₁ := standardOpen (ULift.{u} (Fin 2)) S ⟨1⟩
  let f := LaurentPolynomial.eval₂ (chartConst k (U₀ ⊓ U₁))
    (ratioUnit (ULift.{u} (Fin 2)) S ⟨0⟩ ⟨1⟩)
  obtain ⟨w, hw⟩ := (Units.map_bijective (bijective_overlap_laurent k)).2 v
  obtain ⟨⟨c, n⟩, hc⟩ := (AffinePuncturedLine.affine_punctured_line_algebra k).2.1.2
    (AffinePuncturedLine.specUnitSection (LaurentPolynomial k) w)
  have hcw : AffinePuncturedLine.laurentUnit k c n = w := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).symm
    apply Units.map_injective e.commRingCatIsoToRingEquiv.injective
    exact congrArg (fun z : AffinePuncturedLine.specUnits (LaurentPolynomial k) ↦
      z.toAdd.down.toMul) hc
  have hv : v.val = chartConst k (U₀ ⊓ U₁) c.val *
      (ratioUnit (ULift.{u} (Fin 2)) S ⟨0⟩ ⟨1⟩ ^ n).val := by
    rw [← hw, ← hcw]
    change f (LaurentPolynomial.C c.val * LaurentPolynomial.T n) = _
    simp only [f, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
  refine ⟨n, Units.map (chartConst k U₀).toMonoidHom c⁻¹, ?_⟩
  apply Units.ext
  change (ProjectiveLine S).presheaf.map (homOfLE inf_le_left).op
      (chartConst k U₀ (c⁻¹).val) * v.val = _
  rw [presheaf_map_chartConst, hv, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rfl

end AlgebraicGeometry.ProjectiveLine
