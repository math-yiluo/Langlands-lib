/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits

/-! # Tensor products of cokernel projections of complexes of module sheaves

The total tensor product of complexes of module sheaves preserves cokernels in each
variable, so the tensor product of two cokernel projections is the cokernel of the two
whiskered maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- Left tensoring with a complex of module sheaves preserves finite colimits. -/
instance preservesFiniteColimits_tensorLeft (Z : Complex R) :
    PreservesFiniteColimits (tensorLeft Z) := by
  have : HasColimitsOfSize.{0, 0} (Modules R) := hasColimitsOfSizeShrink.{0, 0, w, w} _
  refine ⟨fun K _ _ ↦ ?_⟩
  have (M : Modules R) : PreservesColimitsOfShape K ((curriedTensor (Modules R)).obj M) :=
    inferInstanceAs (PreservesColimitsOfShape K (tensorLeft M))
  exact inferInstanceAs (PreservesColimitsOfShape K
    ((Functor.map₂HomologicalComplex (curriedTensor (Modules R)) (.up ℤ) (.up ℤ)
      (.up ℤ)).obj Z))

/-- Right tensoring with a complex of module sheaves preserves finite colimits. -/
instance preservesFiniteColimits_tensorRight (Z : Complex R) :
    PreservesFiniteColimits (tensorRight Z) := by
  have : HasColimitsOfSize.{0, 0} (Modules R) := hasColimitsOfSizeShrink.{0, 0, w, w} _
  refine ⟨fun K _ _ ↦ ?_⟩
  have (M : Modules R) :
      PreservesColimitsOfShape K ((curriedTensor (Modules R)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape K (tensorRight M))
  exact inferInstanceAs (PreservesColimitsOfShape K
    ((Functor.map₂HomologicalComplex (curriedTensor (Modules R)) (.up ℤ) (.up ℤ)
      (.up ℤ)).flip.obj Z))

/-- The tensor product of two epimorphisms of complexes of module sheaves is an
epimorphism. -/
theorem epi_tensorHom {A A' B B' : Complex R} (f : A ⟶ A') (g : B ⟶ B') [Epi f] [Epi g] :
    Epi (f ⊗ₘ g) := by
  rw [tensorHom_def]
  have : Epi (f ▷ B) := (tensorRight B).map_epi f
  have : Epi (A' ◁ g) := (tensorLeft A').map_epi g
  infer_instance

/-- If a functor preserves the cokernel of `a`, every map out of `G.obj A` killing `G.map a`
factors through `G.map (cokernel.π a)`. -/
theorem exists_map_cokernelπ_comp {D E : Type*} [Category D] [Category E]
    [HasZeroMorphisms D] [HasZeroMorphisms E] (G : D ⥤ E) [G.PreservesZeroMorphisms]
    {X : E} {A' A : D} (a : A' ⟶ A) [HasCokernel a] [HasCokernel (G.map a)]
    [PreservesColimit (parallelPair a 0) G] (φ : G.obj A ⟶ X) (h : G.map a ≫ φ = 0) :
    ∃ ψ : G.obj (cokernel a) ⟶ X, G.map (cokernel.π a) ≫ ψ = φ :=
  ⟨inv (cokernelComparison a G) ≫ cokernel.desc _ φ h, by
    rw [← π_comp_cokernelComparison_assoc, IsIso.hom_inv_id_assoc, cokernel.π_desc]⟩

/-- A map out of `A ⊗ B` killing `a ▷ B` and `A ◁ b` factors uniquely through the
tensor product of the cokernel projections of `a` and `b`. -/
theorem existsUnique_cokernelπ_tensorHom {A' A B' B X : Complex R} (a : A' ⟶ A) (b : B' ⟶ B)
    (φ : A ⊗ B ⟶ X) (ha : a ▷ B ≫ φ = 0) (hb : A ◁ b ≫ φ = 0) :
    ∃! ψ : cokernel a ⊗ cokernel b ⟶ X,
      (cokernel.π a ⊗ₘ cokernel.π b) ≫ ψ = φ := by
  have : Epi (cokernel.π a ⊗ₘ cokernel.π b) := epi_tensorHom _ _
  have : Epi (cokernel.π a ▷ B') := (tensorRight B').map_epi _
  obtain ⟨φ₁, hφ₁⟩ := exists_map_cokernelπ_comp (tensorRight B) a φ ha
  have hb₁ : cokernel a ◁ b ≫ φ₁ = 0 := by
    rw [← cancel_epi (cokernel.π a ▷ B'), ← whisker_exchange_assoc]
    erw [hφ₁]
    rw [hb, comp_zero]
  obtain ⟨ψ, hψ⟩ := exists_map_cokernelπ_comp (tensorLeft (cokernel a)) b φ₁ hb₁
  have hfac : (cokernel.π a ⊗ₘ cokernel.π b) ≫ ψ = φ := by
    rw [tensorHom_def, Category.assoc]
    erw [hψ, hφ₁]
  refine ⟨ψ, hfac, fun ψ' hψ' ↦ ?_⟩
  rw [← cancel_epi (cokernel.π a ⊗ₘ cokernel.π b), hψ', hfac]

end SheafOfModules.FilteredConvolutionCore
