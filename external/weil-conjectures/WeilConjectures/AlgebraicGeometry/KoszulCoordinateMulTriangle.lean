/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

import WeilConjectures.AlgebraicGeometry.KoszulCoordinateConeIso
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # Multiplication in one Koszul coordinate

Source: Stacks Project, Tags 062C and 09IR.
(blueprint: lem-pc-koszul-coordinate-mul-triangle).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

private theorem triangle_transport
    {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {X Y Z : C}
    (e₁ : X ≅ T.obj₁) (e₂ : Y ≅ T.obj₂) (e₃ : Z ≅ T.obj₃) :
    ∃ (α : X ⟶ Y) (β : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang C := by
  refine ⟨e₁.hom ≫ T.mor₁ ≫ e₂.inv, e₂.hom ≫ T.mor₂ ≫ e₃.inv,
    e₃.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv, ?_⟩
  apply isomorphic_distinguished _ hT
  exact Triangle.isoMk _ T e₁ e₂ e₃
    (by simp [Category.assoc]) (by simp [Category.assoc])
    (by simp [Category.assoc, ← Functor.map_comp])

/-- Replacing one Koszul generator by a product gives a distinguished triangle.
Source: Stacks Project, More on Algebra, Tag 062C (lemma-koszul-mult), and
Derived Categories of Schemes, Tag 09IR (lemma-orthogonal-koszul-complex).
(blueprint: lem-pc-koszul-coordinate-mul-triangle).

Proof: Let `P` be the extended Koszul complex on the coordinates other than `i`.
For each scalar `c`, the coordinate-cone isomorphism identifies the sheafified
Koszul complex with the cone of the sheafified endomorphism `c • id_P`.
Functoriality and the scalar composition law identify the composite of the
endomorphisms for `a` and `b` with the endomorphism for `a * b`.
Mathlib's `mappingConeCompTriangleh_distinguished` gives the distinguished
triangle of these three cones in the homotopy category of sheaf complexes.
The triangulated functor `DerivedCategory.Qh` preserves this triangle.
Compose the localized coordinate-cone isomorphisms with `quotientCompQhIso`
and transport the triangle to the exact three objects in the statement.
All maps and commutativity equations are constructed in this proof. No
regularity, nonvanishing, or quasi-coherence hypothesis is needed. For `r = 0`
there is no coordinate `i`; zero scalars and the zero ring are included.
-/
theorem koszul_coordinate_mul_triangle
    (A : Type u) [CommRing A] (r : ℕ) (g : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (i : Fin r) (a b : A) :
    let K := fun g' : Fin r → A ↦ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r g').extend
          ComplexShape.embeddingDownNat))
    ∃ (α : K (Function.update g i a) ⟶ K (Function.update g i (a * b)))
      (β : K (Function.update g i (a * b)) ⟶ K (Function.update g i b))
      (δ : K (Function.update g i b) ⟶ (K (Function.update g i a))⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (schemeDerivedCategory (Spec (.of A))) := by
  classical
  rcases r with _ | r
  · exact Fin.elim0 i
  · let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
    let F := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) C
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
    let P := (ExteriorAlgebra.koszulComplex A r (fun j ↦ g (i.succAbove j))).extend
      ComplexShape.embeddingDownNat
    let μ := fun c : A ↦ F.map (c • 𝟙 P)
    have hmul : μ a ≫ μ b = μ (a * b) := by
      dsimp only [μ]
      rw [← F.map_comp]
      congr 1
      simp [Linear.comp_smul, smul_smul, mul_comm]
    obtain ⟨ea⟩ := koszul_coordinate_cone_iso A r g i a
    obtain ⟨eb⟩ := koszul_coordinate_cone_iso A r g i b
    obtain ⟨eab⟩ := koszul_coordinate_cone_iso A r g i (a * b)
    let T := DerivedCategory.Qh.mapTriangle.obj
      (CochainComplex.mappingConeCompTriangleh (μ a) (μ b))
    have hT : T ∈ distTriang (schemeDerivedCategory (Spec (.of A))) :=
      DerivedCategory.Qh.map_distinguished _
        (HomotopyCategory.mappingConeCompTriangleh_distinguished (μ a) (μ b))
    let ea' := DerivedCategory.Q.mapIso ea ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _
    let eb' := DerivedCategory.Q.mapIso eb ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _
    let eab' := DerivedCategory.Q.mapIso (eab ≪≫
      eqToIso (congrArg (fun t : F.obj P ⟶ F.obj P ↦ CochainComplex.mappingCone t)
        hmul.symm)) ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app _
    exact triangle_transport T hT ea' eab' eb'

end AlgebraicGeometry
