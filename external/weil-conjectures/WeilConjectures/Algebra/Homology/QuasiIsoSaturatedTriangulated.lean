/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.Mathlib.Algebra.Homology.Localization

/-!
# Quasi-isomorphisms as a saturated triangulated multiplicative system

Source: Stacks Project, Lemma 05RT and Situation 05S8
(blueprint: lem-pur-quasi-isos-saturated-triangulated).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Pretriangulated

namespace HomotopyCategory

/-- Quasi-isomorphisms in the homotopy category of integer-indexed cochain complexes form a
saturated multiplicative system compatible with its triangulated structure. The two fraction
calculi express MS1--MS3; compatibility with the triangulation expresses MS4 (its parent,
compatibility with shifts) and MS5 (completion of morphisms of distinguished triangles); the
following compositional implication expresses MS6.
They also satisfy two-out-of-three, are closed under retracts, and are characterized by acyclic
cones. The derived-category functor is an exact localization. These are the category and
multiplicative-system hypotheses in Stacks Situation 05S8.

Source: Stacks Project, Lemma 05RT, Definitions 04VB--04VD and 05R2, and Situation 05S8
(blueprint: lem-pur-quasi-isos-saturated-triangulated).

Proof outline:
1. Homotopic maps induce equal cohomology maps, so the quasi-isomorphism class is well defined.
   Apply `lem-pc-quasi-isomorphisms-multiplicative-system` for both fraction calculi and the
   localization description of the derived category.
2. Use `lem-pur-homotopy-category-triangulated` for the triangulated structure on the homotopy
   category and exactness of the localization functor.
3. Shifting by `n` replaces cohomology in degree `r` by cohomology in degree `r + n`, proving MS4.
4. Complete the square to a morphism of distinguished triangles by TR3. Applying cohomology
   gives a ladder of long exact sequences, by `lem-sf-derived-homology-long-exact` and
   `lem-weil-pbc-derived-cohomology-ladder`. The four surrounding vertical maps are isomorphisms,
   so `lem-weil-pbc-five-lemma` makes the third triangle map a quasi-isomorphism (MS5).
5. Apply each cohomology functor for MS6: invertibility of the two composites gives both a left
   and a right inverse for the middle map. Two-out-of-three and stability under retracts follow
   from the corresponding properties of isomorphisms on each cohomology object.
6. Apply `lem-pur-quasi-iso-cone-acyclic` for the cone criterion.
7. Together these give the saturated, triangulation-compatible system and exact localization,
   hence the category and system requirements in Situation 05S8. -/
theorem quasiIso_saturated_triangulated (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    (quasiIso A (ComplexShape.up ℤ)).HasLeftCalculusOfFractions ∧
    (quasiIso A (ComplexShape.up ℤ)).HasRightCalculusOfFractions ∧
    (quasiIso A (ComplexShape.up ℤ)).IsCompatibleWithTriangulation ∧
    (∀ (W X Y Z : HomotopyCategory A (ComplexShape.up ℤ))
      (f : X ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z),
      quasiIso A (ComplexShape.up ℤ) (f ≫ h) → quasiIso A (ComplexShape.up ℤ) (g ≫ f) →
        quasiIso A (ComplexShape.up ℤ) f) ∧
    (quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty ∧
    (quasiIso A (ComplexShape.up ℤ)).IsStableUnderRetracts ∧
    (∀ (T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))),
      T ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) →
        (quasiIso A (ComplexShape.up ℤ) T.mor₁ ↔ subcategoryAcyclic A T.obj₃)) ∧
    (DerivedCategory.Qh (C := A)).IsLocalization (quasiIso A (ComplexShape.up ℤ)) ∧
    (DerivedCategory.Qh (C := A)).IsTriangulated := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, inferInstance, inferInstance⟩
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · intro W X Y Z f g h hfh hgf n
    have hfh' : IsIso ((homologyFunctor A (ComplexShape.up ℤ) n).map f ≫
        (homologyFunctor A (ComplexShape.up ℤ) n).map h) := by
      simpa only [Functor.map_comp] using hfh n
    have hgf' : IsIso ((homologyFunctor A (ComplexShape.up ℤ) n).map g ≫
        (homologyFunctor A (ComplexShape.up ℤ) n).map f) := by
      simpa only [Functor.map_comp] using hgf n
    have : Mono ((homologyFunctor A (ComplexShape.up ℤ) n).map f) :=
      mono_of_mono ((homologyFunctor A (ComplexShape.up ℤ) n).map f)
        ((homologyFunctor A (ComplexShape.up ℤ) n).map h)
    have : Epi ((homologyFunctor A (ComplexShape.up ℤ) n).map f) :=
      epi_of_epi ((homologyFunctor A (ComplexShape.up ℤ) n).map g)
        ((homologyFunctor A (ComplexShape.up ℤ) n).map f)
    exact isIso_of_mono_of_epi _
  · infer_instance
  · refine ⟨?_⟩
    intro X Y Z W f g h hg n
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms A)
      (h.map (homologyFunctor A (ComplexShape.up ℤ) n)) (hg n)
  · intro T hT
    rw [quasiIso_eq_trW_subcategoryAcyclic]
    exact (subcategoryAcyclic A).trW_iff_of_distinguished T hT

end HomotopyCategory
