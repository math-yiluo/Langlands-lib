/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Evaluation functors of homological complexes are adjoints

The evaluation functor `HomologicalComplex.eval C c i₁` is a left adjoint as soon as there is
`i₀ ≠ i₁` with `c.Rel i₀ i₁`: the functor `K ↦ (K.X i₁ ⟶ X)` is represented by
`double (𝟙 X) hi₀₁`. In particular, for cochain complexes indexed by `ℤ`, colimits are
computed degreewise without any assumption on `C`.

## Main statements

- `HomologicalComplex.isLeftAdjoint_eval`, `HomologicalComplex.isRightAdjoint_eval`.
- `HomologicalComplex.isColimitCofanMkX`, `HomologicalComplex.isLimitFanMkX`.
- `CochainComplex.isLeftAdjoint_eval`.
-/

@[expose] public section

open CategoryTheory Limits Category Opposite

namespace HomologicalComplex

section Double

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {X₀ X₁ : C} {f : X₀ ⟶ X₁} {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)
  (h : i₀ ≠ i₁) {K : HomologicalComplex C c} (φ₀ : K.X i₀ ⟶ X₀) (φ₁ : K.X i₁ ⟶ X₁)
  (comm : K.d i₀ i₁ ≫ φ₁ = φ₀ ≫ f)
  (hφ : ∀ (k : ι), c.Rel k i₀ → K.d k i₀ ≫ φ₀ = 0)

open scoped Classical in
/-- Constructor for morphisms to a homological complex `double f hi₀₁`. -/
noncomputable def mkHomToDouble : K ⟶ double f hi₀₁ where
  f k :=
    if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ φ₀ ≫ (doubleXIso₀ f hi₀₁).inv ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ φ₁ ≫ (doubleXIso₁ f hi₀₁ h).inv ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₁ : k₁ = i₁
    · subst h₁
      rw [dite_eq_right h.symm, dite_eq_left rfl]
      obtain rfl := c.prev_eq hk hi₀₁
      simp [double_d f hi₀₁ h, comm]
    · rw [double_d_eq_zero₁ _ _ _ _ h₁, comp_zero]
      by_cases h₀ : k₁ = i₀
      · subst h₀
        dsimp
        rw [ite_eq_left rfl, id_comp, comp_id, reassoc_of% (hφ k₀ hk), zero_comp]
      · apply (isZero_double_X f hi₀₁ k₁ h₀ h₁).eq_of_tgt

@[simp, reassoc]
lemma mkHomToDouble_f₀ :
    (mkHomToDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₀ = φ₀ ≫ (doubleXIso₀ f hi₀₁).inv := by
  dsimp [mkHomToDouble]
  rw [ite_eq_left rfl, id_comp, comp_id]

@[simp, reassoc]
lemma mkHomToDouble_f₁ :
    (mkHomToDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₁ = φ₁ ≫ (doubleXIso₁ f hi₀₁ h).inv := by
  dsimp [mkHomToDouble]
  rw [dite_eq_right h.symm, ite_eq_left rfl, id_comp, comp_id]

variable {hi₀₁} in
/-- Morphisms `K ⟶ double (𝟙 X) hi₀₁` identify with morphisms `K.X i₁ ⟶ X`. -/
@[simps]
noncomputable def homToDoubleIdEquiv (K : HomologicalComplex C c) (X : C) :
    (K ⟶ double (𝟙 X) hi₀₁) ≃ (K.X i₁ ⟶ X) where
  toFun g := g.f i₁ ≫ (doubleXIso₁ _ hi₀₁ h).hom
  invFun φ₁ := mkHomToDouble _ h (K.d i₀ i₁ ≫ φ₁) φ₁ (by simp) (by simp)
  left_inv g := by
    ext
    · simp [← g.comm_assoc, double_d _ _ h]
    · simp
  right_inv _ := by simp

/-- For `hi₀₁ : c.Rel i₀ i₁` with `i₀ ≠ i₁` and `X : C`, the functor which sends
`K : HomologicalComplex C c` to `K.X i₁ ⟶ X` is representable by `double (𝟙 X) hi₀₁`. -/
noncomputable def evalOpCompYonedaRepresentableByDoubleId (X : C) :
    ((eval C c i₁).op ⋙ yoneda.obj X).RepresentableBy (double (𝟙 X) hi₀₁) where
  homEquiv {K} := homToDoubleIdEquiv h K X
  homEquiv_comp _ _ := assoc _ _ _

end Double

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

/-- If `c.Rel i₀ i₁` with `i₀ ≠ i₁`, the evaluation functor `eval C c i₁` is a left adjoint. In
particular, it preserves all colimits. -/
lemma isLeftAdjoint_eval [HasZeroMorphisms C] [HasZeroObject C] {i₀ i₁ : ι}
    (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁) : (eval C c i₁).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (by
    ext X
    simpa using ⟨_, ⟨evalOpCompYonedaRepresentableByDoubleId hi₀₁ h X⟩⟩)

/-- If `c` has no loop, the evaluation functor `eval C c j` is a right adjoint. In particular,
it preserves all limits. -/
instance isRightAdjoint_eval [HasZeroMorphisms C] [HasZeroObject C] [c.HasNoLoop] (j : ι) :
    (eval C c j).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (by
    ext X
    simpa using ⟨_, ⟨evalCompCoyonedaCorepresentable c X j⟩⟩)

section Degreewise

variable [HasZeroMorphisms C] {β : Type*} {K : β → HomologicalComplex C c}

/-- A coproduct of homological complexes is a coproduct in each degree, provided the evaluation
functors preserve it. -/
noncomputable def isColimitCofanMkX {s : Cofan K} (hs : IsColimit s) (i : ι)
    [PreservesColimit (Discrete.functor K) (eval C c i)] :
    IsColimit (Cofan.mk (s.pt.X i) fun j ↦ (s.inj j).f i) :=
  isColimitCofanMkObjOfIsColimit (eval C c i) K s.inj
    (hs.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp)))

/-- A product of homological complexes is a product in each degree, provided the evaluation
functors preserve it. -/
noncomputable def isLimitFanMkX {s : Fan K} (hs : IsLimit s) (i : ι)
    [PreservesLimit (Discrete.functor K) (eval C c i)] :
    IsLimit (Fan.mk (s.pt.X i) fun j ↦ (s.proj j).f i) :=
  isLimitFanMkObjOfIsLimit (eval C c i) K s.proj
    (hs.ofIsoLimit (Fan.ext (Iso.refl _) (by simp)))

@[reassoc (attr := simp)]
lemma inj_f_desc_isColimitCofanMkX {s : Cofan K} (hs : IsColimit s) (i : ι)
    [PreservesColimit (Discrete.functor K) (eval C c i)] {A : C} (f : ∀ j, (K j).X i ⟶ A)
    (j : β) : (s.inj j).f i ≫ Cofan.IsColimit.desc (isColimitCofanMkX hs i) f = f j :=
  Cofan.IsColimit.fac (isColimitCofanMkX hs i) f j

@[reassoc (attr := simp)]
lemma lift_isLimitFanMkX_proj_f {s : Fan K} (hs : IsLimit s) (i : ι)
    [PreservesLimit (Discrete.functor K) (eval C c i)] {A : C} (f : ∀ j, A ⟶ (K j).X i)
    (j : β) : Fan.IsLimit.lift (isLimitFanMkX hs i) f ≫ (s.proj j).f i = f j :=
  Fan.IsLimit.fac (isLimitFanMkX hs i) f j

end Degreewise

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- For cochain complexes indexed by `ℤ`, the evaluation functors are left adjoints, so that
colimits of cochain complexes are computed degreewise. -/
instance isLeftAdjoint_eval (n : ℤ) :
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).IsLeftAdjoint :=
  HomologicalComplex.isLeftAdjoint_eval (c := .up ℤ) (i₀ := n - 1) (by simp) (by omega)

end CochainComplex
