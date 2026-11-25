/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteOrderedCechCoefficientMap
import WeilConjectures.AlgebraicGeometry.FiniteOrderedCechTotalMap

/-! # The ordered Čech coefficient map is a quasi-isomorphism

Source: Stacks Project, Cohomology, Tag 01ET.
(auxiliary; not a blueprint node)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Sectionwise quasi-isomorphisms on all intersections suffice for beta.
Source: Stacks Project, Tag 01ET.
(auxiliary; not a blueprint node)
Proof: Restrict each section augmentation to the global ring. The finite-column
Čech comparison makes the map on totals a quasi-isomorphism. The total of the
single coefficient sheaf is canonically its ordered Čech complex, by the sole
nonzero resolution-degree-zero summands. Naturality identifies the composite
with the specified coefficient map. -/
theorem orderedCechCoefficientMap_quasiIso
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (.up ℤ) 0).obj F ⟶ G)
    (r : ℕ) (V : Fin r → X.Opens)
    (hsections : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj
          (op (alternatingCechIntersection V t))).mapHomologicalComplex (.up ℤ)).map e)) :
    QuasiIso (orderedCechCoefficientMap V e) := by
  let S := (HomologicalComplex.single
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj F
  have hmap : QuasiIso ((alternatingCechTotalFunctor V).map e) :=
    orderedCechTotalMap_quasiIso X r V S G e hsections
  have hj := orderedCechCoefficientMap_single_isIso V F
  have heq : orderedCechCoefficientMap V (𝟙 S) ≫
      (alternatingCechTotalFunctor V).map e = orderedCechCoefficientMap V e := by
    have h := orderedCechCoefficientMap_naturality V (𝟙 S) e (𝟙 F) e (by
      simp only [HomologicalComplex.id_f, Category.id_comp]
      exact Category.id_comp _)
    simpa using h
  rw [← heq]
  infer_instance

end
end AlgebraicGeometry
