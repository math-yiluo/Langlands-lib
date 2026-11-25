/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalSectionTotalComparison
/-! # Normalized internal-to-sectionwise derived tensor comparison

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (auxiliary; not a blueprint node).

## Main definitions

* `TensorComparison`: the canonical tensor comparison, normalized on K-flat models.
* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

/-- The same representative square, retaining heterogeneous equality at its endpoints.
Source: Stacks 06YS, 08J9
(auxiliary; not a blueprint node).
This generic predicate names the complete normalization before coefficient
specialization, including its fixed total map and representative model. -/
def tensorLocalizationSquareHEq
    {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₁} [Category.{v₁} D₀]
    {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
    (qC : C₀ ⥤ C) (qD : D₀ ⥤ D) (f₀ : C₀ ⥤ D₀) (f : C ⥤ D)
    (factor : qC ⋙ f ≅ f₀ ⋙ qD)
    (t : C × C ⥤ C) (t₀ : C₀ × C₀ ⥤ C₀)
    (s : D × D ⥤ D) (s₀ : D₀ × D₀ ⥤ D₀)
    (μ : ∀ P Q : C₀, t.obj (qC.obj P, qC.obj Q) ⟶ qC.obj (t₀.obj (P, Q)))
    (c : ∀ P Q : C₀, f₀.obj (t₀.obj (P, Q)) ≅ s₀.obj (f₀.obj P, f₀.obj Q))
    (flat : D₀ → Prop)
    (model : ∀ (P Q : D₀), flat P → flat Q →
      (qD.obj (s₀.obj (P, Q)) ≅ s.obj (qD.obj P, qD.obj Q)))
    (iso : t ⋙ f ≅ (f.prod f) ⋙ s) : Prop :=
  ∀ (P Q : C₀) (hP : flat (f₀.obj P)) (hQ : flat (f₀.obj Q)),
    HEq (iso.hom.app (qC.obj P, qC.obj Q) ≫
      s.map (X := (f.obj (qC.obj P), f.obj (qC.obj Q)))
        (Y := (qD.obj (f₀.obj P), qD.obj (f₀.obj Q)))
        (factor.hom.app P, factor.hom.app Q))
      (f.map (μ P Q) ≫ factor.hom.app (t₀.obj (P, Q)) ≫
        qD.map (c P Q).hom ≫ (model (f₀.obj P) (f₀.obj Q) hP hQ).hom)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
