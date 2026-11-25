/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex of a single object over `V`, with coefficients in a preadditive category

Let `C` be a category, `V` an object of `C` such that `Over V` has finite products, and `U₀` an
object of `Over V`. For a presheaf `P` on `C` with values in a preadditive category `A`, the
Čech complex `Č(U₀, P)` has in degree `k` the object `P(U₀ ×_V ⋯ ×_V U₀)` (`k + 1` factors), and
its differential is the alternating sum of the restrictions along the projections forgetting
one factor. It is the alternating coface map complex of the cosimplicial object obtained by
evaluating `P` on the Čech conerve of `U₀`.

This is the single-object case of `CategoryTheory.Presheaf.cechComplex`, which is only defined
for presheaves of abelian groups, for an arbitrary preadditive coefficient category.

## Main definitions

- `CategoryTheory.Presheaf.cechConerve`: the Čech nerve `[k] ↦ U₀ ×_V ⋯ ×_V U₀` of `U₀`, as a
  functor `SimplexCategory ⥤ (Over V)ᵒᵖ`.
- `CategoryTheory.Presheaf.overCechComplex`: the Čech complex `Č(U₀, P)`, as a functor of `P`.
-/

@[expose] public section

universe w v v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] (U₀ : Over V)

/-- The Čech nerve `[k] ↦ U₀ ×_V ⋯ ×_V U₀` (`k + 1` factors) of an object `U₀` over `V`, as a
functor `SimplexCategory ⥤ (Over V)ᵒᵖ`: a map `θ : [k] ⟶ [m]` acts by the projection
`U₀^{m + 1} ⟶ U₀^{k + 1}` with components the projections of index `θ l`. -/
@[simps]
noncomputable def cechConerve : SimplexCategory ⥤ (Over V)ᵒᵖ where
  obj k := op (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (k.len + 1) ↦ 0))
  map {_ m} θ :=
    (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (m.len + 1) ↦ 0) θ.toOrderHom).op
  map_id k := Quiver.Hom.unop_inj (by exact cechNerveMap_id (fun _ : Fin 1 ↦ U₀) _)
  map_comp θ θ' := Quiver.Hom.unop_inj (by
    exact (cechNerveMap_comp (fun _ : Fin 1 ↦ U₀) _ θ.toOrderHom θ'.toOrderHom).symm)

variable {A : Type u'} [Category.{v'} A]

/-- The Čech cosimplicial object `[k] ↦ P(U₀ ×_V ⋯ ×_V U₀)` of `U₀` with values in a presheaf
`P`, as a functor of `P`. -/
noncomputable def overCechCosimplicialObject : (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  (Functor.whiskeringLeft _ _ _).obj (cechConerve U₀ ⋙ (Over.forget V).op)

variable [Preadditive A]

/-- The Čech complex `Č(U₀, P)` of an object `U₀` over `V` with values in a presheaf `P`, as a
functor of `P`: the alternating coface map complex of
`CategoryTheory.Presheaf.overCechCosimplicialObject`. -/
noncomputable def overCechComplex : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  overCechCosimplicialObject U₀ ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

variable (P : Cᵒᵖ ⥤ A)

lemma overCechComplex_obj_X (k : ℕ) : ((overCechComplex U₀).obj P).X k =
    P.obj (op (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (k + 1) ↦ 0)).left) :=
  rfl


/-- The Čech differential is the alternating sum of the restrictions along the faces. -/
lemma overCechComplex_obj_d (k : ℕ) : ((overCechComplex U₀).obj P).d k (k + 1) =
    ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • P.map
      (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (k + 2) ↦ 0) i.succAbove).left.op := by
  have h : ((overCechComplex U₀).obj P).d k (k + 1) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((overCechCosimplicialObject U₀).obj P).δ i :=
    CochainComplex.of_d (fun m ↦ ((overCechCosimplicialObject U₀).obj P).obj (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) k
  rw [h]
  rfl

lemma overCechComplex_map_f {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) (k : ℕ) :
    ((overCechComplex U₀).map φ).f k =
      φ.app (op (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (k + 1) ↦ 0)).left) :=
  rfl

instance : (overCechComplex (A := A) U₀).Additive where
  map_add := rfl

/-- The augmentation `P(V) ⟶ P(U₀)` of the Čech complex `Č(U₀, P)`, the restriction along the
structure morphism of `U₀ ×_V ⋯ ×_V U₀` with one factor. -/
noncomputable def overCechAugmentation : P.obj (op V) ⟶ ((overCechComplex U₀).obj P).X 0 :=
  P.map (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 1 ↦ 0)).hom.op

@[reassoc (attr := simp)]
lemma overCechAugmentation_d : overCechAugmentation U₀ P ≫ ((overCechComplex U₀).obj P).d 0 1 =
    0 := by
  rw [overCechComplex_obj_d, Fin.sum_univ_two, Preadditive.comp_add, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, overCechAugmentation, ← P.map_comp, ← P.map_comp, ← op_comp,
    ← op_comp, Over.w, Over.w]
  simp

end CategoryTheory.Presheaf
