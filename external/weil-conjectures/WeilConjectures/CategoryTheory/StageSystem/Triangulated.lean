/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.IdempotentComplete
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The pair category of a system of triangulated categories

If all the stages of a stage system with triangulated transition functors are triangulated
(octahedral axiom), so is the pair category: two composable morphisms of the pair category are
represented at a common stage, and the octahedron of the representatives maps to an octahedron
of the pair category under the triangulated inclusion of that stage (TR4).

Combined with `CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`, the pair category
of a stage system of idempotent complete triangulated categories is an idempotent complete
triangulated category, and the functor to its Karoubi envelope is an exact equivalence.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.isTriangulated`.
- `CategoryTheory.StageSystem.PairCategory.verdier_axioms`.
- `CategoryTheory.StageSystem.PairCategory.idempotentComplete_triangulation`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated Triangulated Idempotents

namespace Pretriangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An octahedron for a composite `u₁₃` equal to `u₁₂ ≫ u₂₃` gives an octahedron for the
composite `u₁₂ ≫ u₂₃` itself. -/
lemma nonempty_octahedron_rfl {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : D} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃}
    {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃) {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧}
    {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang D} {v₂₃ : X₃ ⟶ Z₂₃}
    {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang D}
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang D}
    (H : Octahedron comm h₁₂ h₂₃ h₁₃) (h₁₃' : Triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ distTriang D) :
    Nonempty (Octahedron rfl h₁₂ h₂₃ h₁₃') := by
  subst comm
  exact ⟨H⟩

end Pretriangulated

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] {S : StageSystem C}
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ] [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]

namespace PairCategory

/-- The octahedral axiom TR4: if all the stages are triangulated, so is the pair category. -/
instance isTriangulated [∀ i, IsTriangulated (C i)] : IsTriangulated S.PairCategory :=
  IsTriangulated.mk' fun X₁ X₂ X₃ u₁₂ u₂₃ ↦ by
    obtain ⟨n, -, hX₁, hX₂, hX₂', hX₃, a, b, rfl, rfl⟩ := exists_common_stage u₁₂ u₂₃ X₁.stage
    obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle a
    obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle b
    obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (a ≫ b)
    have H := (someOctahedron rfl h₁₂ h₂₃ h₁₃).map (S.ι n)
    have hd : Triangle.mk ((S.ι n).map (a ≫ b)) ((S.ι n).map v₁₃)
        ((S.ι n).map w₁₃ ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _) ∈
          distTriang S.PairCategory := (S.ι n).map_distinguished _ h₁₃
    have h₁₃' : Triangle.mk ((S.ι n).map a ≫ (S.ι n).map b) ((S.ι n).map v₁₃)
        ((S.ι n).map w₁₃ ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _) ∈
          distTriang S.PairCategory :=
      Pretriangulated.isomorphic_distinguished _ hd _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp))
    exact ⟨_, _, _, _, _, _, (S.ι n).map a, (S.ι n).map b, S.isoToStage X₁ hX₁,
      S.isoToStage X₂ hX₂, S.isoToStage X₃ hX₃, by simp [mkHom_eq_isoToStage],
      by simp [mkHom_eq_isoToStage], _, _, (S.ι n).map_distinguished _ h₁₂, _, _,
      (S.ι n).map_distinguished _ h₂₃, _, _, h₁₃', nonempty_octahedron_rfl _ H h₁₃'⟩

/-- The functor from the pair category to its Karoubi envelope is triangulated. -/
lemma isTriangulated_toKaroubi : (toKaroubi S.PairCategory).IsTriangulated := inferInstance

/-- Verdier axioms and stagewise triangulation. For a stage system of triangulated categories with
triangulated transition functors, the pair category is triangulated (its pretriangulated structure
being `CategoryTheory.StageSystem.PairCategory.pretriangulated`), every stage inclusion `ι i` is a
triangulated functor, and the identifications `T_{j/i} ⋙ ι j ≅ ι i` commute with the shifts. -/
theorem verdier_axioms [∀ i, IsTriangulated (C i)] :
    IsTriangulated S.PairCategory ∧ (∀ i, (S.ι i).IsTriangulated) ∧
      ∀ (i j : I) (h : i ≤ j), NatTrans.CommShift (S.transIso h).hom ℤ :=
  ⟨inferInstance, fun _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩

/-- Idempotent-complete triangulation. For a stage system of idempotent complete triangulated
categories with triangulated transition functors, the pair category is an idempotent complete
triangulated category, the canonical functor to its Karoubi envelope is an equivalence and is
triangulated, and the stage inclusions `ι i` are triangulated functors.

The linearity statement of the blueprint (`ℚ̄_ℓ`-linearity of the pair category and
`E`-linearity of the inclusions) involves coefficient fields varying with the stage and is not
part of this abstract statement. -/
theorem idempotentComplete_triangulation [∀ i, IsTriangulated (C i)]
    [∀ i, IsIdempotentComplete (C i)] :
    IsTriangulated S.PairCategory ∧ IsIdempotentComplete S.PairCategory ∧
      (toKaroubi S.PairCategory).IsEquivalence ∧ (toKaroubi S.PairCategory).IsTriangulated ∧
        ∀ i, (S.ι i).IsTriangulated :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun _ ↦ inferInstance⟩

end PairCategory

end StageSystem

end CategoryTheory
