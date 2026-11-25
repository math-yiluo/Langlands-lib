/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Functor

/-! # Total-tensor augmentation components

Source: Stacks Project, Tags 099M and 0913.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open MonoidalCategory

section TensorAugmentation

variable {E : Type*} [Category E] [Abelian E] [HasCountableCoproducts E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E]

/-- The degree-zero total-tensor quotient component, defined by coproduct descent.
Source: Stacks Project, Tag 099M.
(auxiliary; not a blueprint node). -/
def quotientTensorComponent (P D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (F : E ⥤ E) (η : 𝟭 E ⟶ F) (t : ℤ) :
    (HomologicalComplex.mapBifunctor P D (curriedTensor E) (.up ℤ)).X t ⟶ F.obj (P.X t) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦
    if hq : q = 0 then
      (P.X p) ◁ (eqToHom (congrArg D.X hq) ≫ e.hom) ≫
        (ρ_ (P.X p)).hom ≫ η.app (P.X p) ≫
          F.map (eqToHom (congrArg P.X (by change p + q = t at h; omega)))
    else 0)

omit [MonoidalClosed E] in
@[reassoc] private theorem quotientTensorComponent_ι (P D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (F : E ⥤ E) (η : 𝟭 E ⟶ F) (p : ℤ) :
    HomologicalComplex.ιMapBifunctor P D (curriedTensor E) (.up ℤ) p 0 p (by simp) ≫
        quotientTensorComponent P D e F η p =
      (P.X p) ◁ e.hom ≫ (ρ_ (P.X p)).hom ≫ η.app (P.X p) := by
  simp [quotientTensorComponent]

omit [MonoidalClosed E] in
@[reassoc] private theorem quotientTensorComponent_ι_zero (P D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (F : E ⥤ E) (η : 𝟭 E ⟶ F)
    (p q t : ℤ) (h : p + q = t) (hq : q ≠ 0) :
    HomologicalComplex.ιMapBifunctor P D (curriedTensor E) (.up ℤ) p q t h ≫
        quotientTensorComponent P D e F η t = 0 := by
  simp [quotientTensorComponent, hq]

omit [MonoidalClosed E] in
/-- The augmentation supported on Koszul degree zero is a cochain map when the
incoming differential is killed by the reduction unit.
Source: Stacks Project, Tag 099M, construction of the Koszul augmentation; Tag 0913.
(auxiliary; not a blueprint node).

Proof: test the equation on every total-tensor summand. Degree zero gives the
naturality equation for the reduction unit, degree minus one gives the assumed
vanishing of the incoming differential, and all remaining summands are zero. -/
theorem quotientTensorComponent_comm (P D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (F : E ⥤ E) (η : 𝟭 E ⟶ F)
    (hz : ∀ M : E, M ◁ (D.d (-1) 0 ≫ e.hom) ≫ (ρ_ M).hom ≫ η.app M = 0)
    (t : ℤ) :
    quotientTensorComponent P D e F η t ≫ F.map (P.d t (t + 1)) =
      (HomologicalComplex.mapBifunctor P D (curriedTensor E) (.up ℤ)).d t (t + 1) ≫
        quotientTensorComponent P D e F η (t + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hsum : p + q = t := hpq
  simp only [HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show p + 1 = p + 1 from rfl)
      q (t + 1) (by change (p + 1) + q = t + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (show q + 1 = q + 1 from rfl)
      (t + 1) (by change p + (q + 1) = t + 1; omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  by_cases hq : q = 0
  · subst q
    have hp : p = t := by omega
    subst p
    simp only [show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (t, 0) = 1 from rfl,
      one_smul, quotientTensorComponent_ι_assoc, quotientTensorComponent_ι,
      Int.reduceAdd]
    rw [quotientTensorComponent_ι_zero P D e F η t 1 (t + 1) rfl (by decide)]
    simp only [comp_zero, smul_zero, add_zero, curriedTensor_map_app]
    rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
    exact congrArg ((P.X t) ◁ e.hom ≫ (ρ_ (P.X t)).hom ≫ ·)
      (η.naturality (P.d t (t + 1))).symm
  · rw [quotientTensorComponent_ι_zero_assoc P D e F η p q t hsum hq]
    rw [quotientTensorComponent_ι_zero P D e F η (p + 1) q (t + 1)
      (by omega) hq]
    simp only [comp_zero, smul_zero, zero_add, zero_comp]
    by_cases hq' : q + 1 = 0
    · have hq'' : q = -1 := by omega
      subst q
      have hp : p = t + 1 := by omega
      subst p
      change 0 = ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (t + 1, -1) •
        ((P.X (t + 1)) ◁ D.d (-1) 0 ≫
          HomologicalComplex.ιMapBifunctor P D (curriedTensor E) (.up ℤ)
            (t + 1) 0 (t + 1) (by simp) ≫
          quotientTensorComponent P D e F η (t + 1))
      rw [quotientTensorComponent_ι, ← MonoidalCategory.whiskerLeft_comp_assoc,
        hz, smul_zero]
    · rw [quotientTensorComponent_ι_zero P D e F η p (q + 1) (t + 1)
        (by omega) hq']
      simp only [comp_zero, smul_zero]

omit [MonoidalClosed E] in
private theorem quotientTensorComponent_naturality (P P' D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (F : E ⥤ E) (η : 𝟭 E ⟶ F) (f : P ⟶ P') (t : ℤ) :
    (HomologicalComplex.mapBifunctorMap f (𝟙 D) (curriedTensor E) (.up ℤ)).f t ≫
        quotientTensorComponent P' D e F η t =
      quotientTensorComponent P D e F η t ≫ F.map (f.f t) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hsum : p + q = t := hpq
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  by_cases hq : q = 0
  · subst q
    have hp : p = t := by omega
    subst p
    simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp,
      quotientTensorComponent_ι_assoc,
      quotientTensorComponent_ι, curriedTensor_map_app]
    rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
    exact congrArg ((P.X t) ◁ e.hom ≫ (ρ_ (P.X t)).hom ≫ ·) (η.naturality (f.f t))
  · rw [quotientTensorComponent_ι_zero P' D e F η p q t hsum hq,
      quotientTensorComponent_ι_zero_assoc P D e F η p q t hsum hq]
    simp

omit [MonoidalClosed E] in
private theorem quotientTensorComponent_transition (P D D' : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (e' : D'.X 0 ≅ 𝟙_ E) (f : D ⟶ D')
    (hf : f.f 0 ≫ e'.hom = e.hom) (F F' : E ⥤ E)
    (η : 𝟭 E ⟶ F) (η' : 𝟭 E ⟶ F') (τ : F ⟶ F')
    (hη : η ≫ τ = η') (t : ℤ) :
    (HomologicalComplex.mapBifunctorMap (𝟙 P) f (curriedTensor E) (.up ℤ)).f t ≫
        quotientTensorComponent P D' e' F' η' t =
      quotientTensorComponent P D e F η t ≫ τ.app (P.X t) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hsum : p + q = t := hpq
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  by_cases hq : q = 0
  · subst q
    have hp : p = t := by omega
    subst p
    simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
      Category.id_comp, quotientTensorComponent_ι_assoc,
      quotientTensorComponent_ι, curriedTensor_obj_map]
    rw [← whiskerLeft_comp_assoc, hf]
    exact congrArg ((P.X t) ◁ e.hom ≫ (ρ_ (P.X t)).hom ≫ ·)
      (congrArg (fun k ↦ k.app (P.X t)) hη.symm)
  · rw [quotientTensorComponent_ι_zero P D' e' F' η' p q t hsum hq,
      quotientTensorComponent_ι_zero_assoc P D e F η p q t hsum hq]
    simp

private theorem quotientTensorComponent_unit (P D : CochainComplex E ℤ)
    (e : D.X 0 ≅ 𝟙_ E) (u : HomologicalComplex.tensorUnit E (.up ℤ) ⟶ D)
    (hu : u.f 0 ≫ e.hom = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ E)).hom)
    (F : E ⥤ E) (η : 𝟭 E ⟶ F) (t : ℤ) :
    ((HomologicalComplex.rightUnitor P).inv ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor E) (.up ℤ)).f t ≫
        quotientTensorComponent P D e F η t = η.app (P.X t) := by
  simp only [HomologicalComplex.comp_f]
  rw [show (HomologicalComplex.rightUnitor P).inv.f t =
    (ρ_ (P.X t)).inv ≫
      (P.X t) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ E)).inv ≫
        HomologicalComplex.ιMapBifunctor P (HomologicalComplex.tensorUnit E (.up ℤ))
          (curriedTensor E) (.up ℤ) t 0 t (by simp) from
    HomologicalComplex.rightUnitor'_inv P t]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp,
    curriedTensor_obj_map, quotientTensorComponent_ι]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, hu]
  simp

private def complexNatTransOfComponents
    {B E T : Type*} [Category B] [Category E] [HasZeroMorphisms E] [Category T]
    (X Y : B ⥤ CochainComplex (T ⥤ E) ℤ)
    (c : ∀ (P : B) (t : ℤ) (n : T),
      ((X.obj P).X t).obj n ⟶ ((Y.obj P).X t).obj n)
    (hn : ∀ (P : B) (t : ℤ) {m k : T} (f : m ⟶ k),
      ((X.obj P).X t).map f ≫ c P t k = c P t m ≫ ((Y.obj P).X t).map f)
    (hd : ∀ (P : B) (t k : ℤ), (ComplexShape.up ℤ).Rel t k → ∀ n : T,
      c P t n ≫ ((Y.obj P).d t k).app n = ((X.obj P).d t k).app n ≫ c P k n)
    (hp : ∀ {P P' : B} (f : P ⟶ P') (t : ℤ) (n : T),
      ((X.map f).f t).app n ≫ c P' t n = c P t n ≫ ((Y.map f).f t).app n) :
    X ⟶ Y where
  app P :=
    { f := fun t ↦ { app := c P t, naturality := fun {_ _} f ↦ hn P t f }
      comm' := by
        intro t k h
        apply NatTrans.ext
        funext n
        exact hd P t k h n }
  naturality _ _ f := by
    apply HomologicalComplex.hom_ext
    intro t
    apply NatTrans.ext
    funext n
    exact hp f t n

end TensorAugmentation
end CategoryTheory
