/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

/-! # Pure sections of the etale to pro-etale comparison

Source: the monoidal comparison adjunction; Stacks Project, Tag 0GLZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
attribute [local instance] Sheaf.monoidalCategory

private theorem comparison_tensor_sections (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt T).obj U.unop)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      M N).hom.app W
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj (M ⊗ N)).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
            (M ⊗ N)).hom.app U
              ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} A)) M N).app U (x ⊗ₜ[A] y)))) =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M)
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N)).app W
          ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M).obj.map f.op
            (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U x))
          ⊗ₜ[A]
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N).obj.map f.op
            (((ProEtale.comparisonAdjunction
              (ModuleCat.{u + 1} A) T).unit.app N).hom.app U y))) := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let adj := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T
  let i := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let j := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A)
  have h := adj.unit_app_tensor_comp_map_δ M N
  have h₂ := congr_app (Functor.LaxMonoidal.μ_natural i
    (adj.unit.app M) (adj.unit.app N)) U
  have h₃ :
      (Functor.LaxMonoidal.μ i
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).obj (F.obj M))
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).obj (F.obj N))).app U ≫
        (Functor.LaxMonoidal.μ (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T)
          (F.obj M) (F.obj N)).hom.app U =
      (Functor.LaxMonoidal.μ j (F.obj M) (F.obj N)).app ((toProEt T).op.obj U) :=
    Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app.{u + 1,
      u + 1, u + 2, u, u + 1, u}
    (toProEt T) (ModuleCat.{u + 1} A) T.smallEtaleTopology (ProEt.topology T)
    (F.obj M) (F.obj N) U
  have hu : (Functor.LaxMonoidal.μ i M N).app U ≫
      (adj.unit.app (M ⊗ N)).hom.app U ≫
      (Functor.OplaxMonoidal.δ F M N).hom.app ((toProEt T).op.obj U) =
      ((adj.unit.app M).hom.app U ⊗ₘ (adj.unit.app N).hom.app U) ≫
        (Functor.LaxMonoidal.μ j (F.obj M) (F.obj N)).app ((toProEt T).op.obj U) := by
    have hh := congrArg (fun q ↦ (Functor.LaxMonoidal.μ i M N).app U ≫
      (i.map q).app U) h
    simp only [Functor.map_comp, NatTrans.comp_app] at hh
    erw [hh]
    simp only [NatTrans.comp_app, Monoidal.tensorHom_app] at h₂
    erw [← Category.assoc, ← h₂, Category.assoc, h₃]
    rfl
  have hv := ConcreteCategory.congr_hom hu (x ⊗ₜ[A] y)
  have hn := ConcreteCategory.congr_hom
    ((Functor.OplaxMonoidal.δ F M N).hom.naturality f.op)
      ((adj.unit.app (M ⊗ N)).hom.app U
        ((Functor.LaxMonoidal.μ i M N).app U (x ⊗ₜ[A] y)))
  simp only [ModuleCat.comp_apply] at hv hn
  erw [hn, hv]
  exact ConcreteCategory.congr_hom
    ((Functor.LaxMonoidal.μ j (F.obj M) (F.obj N)).naturality f.op) _ |>.symm

private theorem comparison_unit_sections (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : A) :
    (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)).hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj (𝟙_ _)).obj.map f.op
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app (𝟙_ _)).hom.app U
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).app U a))) =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).app W a := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let adj := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T
  have h := adj.unit_app_unit_comp_map_η
  have hε := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app.{u + 1,
      u + 1, u + 2, u + 1, u, u}
    (toProEt T) (ModuleCat.{u + 1} A) T.smallEtaleTopology (ProEt.topology T) U
  have hu := congrArg (fun q ↦
    (Functor.LaxMonoidal.ε (sheafToPresheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A))).app U ≫ q.hom.app U) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  erw [hε] at hu
  have hv := ConcreteCategory.congr_hom hu a
  have hn := ConcreteCategory.congr_hom
    ((Functor.OplaxMonoidal.η F).hom.naturality f.op)
      ((adj.unit.app (𝟙_ _)).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).app U a))
  simp only [ModuleCat.comp_apply] at hv hn
  erw [hn, hv]
  exact ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).naturality f.op) a |>.symm

/-- The comparison adjunction preserves constant scalars and pure tensors on
arbitrary pro-etale tests over etale objects.
Source: Stacks Tag 0GLZ and the monoidal comparison adjunction
(blueprint: lem-amb-comparison-pure-sections).

Proof: apply the tensor axiom for the adjunction unit, then precompose the
underlying presheaf tensor inclusion. Naturality of that inclusion and the
component formula for the continuous direct-image tensor map give the tensor
formula over U. Naturality along f gives the formula over W. The unit axiom
of the same adjunction, followed by the direct-image unit formula, identifies
constant scalars over U. Naturality of the constant-presheaf sheafification
unit gives their formula over W. No flatness or root lifting is required. -/
theorem comparison_pure_sections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (∀ (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt T).obj U.unop)
    (x : M.obj.obj U) (y : N.obj.obj U),
      (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      M N).hom.app W
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj (M ⊗ N)).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
            (M ⊗ N)).hom.app U
              ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} A)) M N).app U (x ⊗ₜ[A] y)))) =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M)
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N)).app W
          ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M).obj.map f.op
            (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U x))
          ⊗ₜ[A]
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N).obj.map f.op
            (((ProEtale.comparisonAdjunction
              (ModuleCat.{u + 1} A) T).unit.app N).hom.app U y)))) ∧
    (∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : A),
      (Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)).hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj (𝟙_ _)).obj.map f.op
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app (𝟙_ _)).hom.app U
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).app U a))) =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of.{u + 1, u + 1} A A))).app W a) := by
  constructor
  · intro M N U W f x y
    exact comparison_tensor_sections A T M N U W f x y
  · intro U W f a
    exact comparison_unit_sections A T U W f a

end AlgebraicGeometry.Scheme
