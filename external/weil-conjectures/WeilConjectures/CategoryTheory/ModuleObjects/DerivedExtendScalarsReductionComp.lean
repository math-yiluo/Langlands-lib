/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransition

/-!
# Reduction of a composite

The reduction `Mod.derivedExtendScalarsReduction` of a composite `S' ⊗ᴸ_R f ≫ s` is
`S ⊗ᴸ_R f` followed by the reduction of `s`
(`Mod.derivedExtendScalarsReduction_map_comp`): reduction commutes with precomposition by the
extension of scalars of a morphism. In particular the reduction of a retraction invariant under
the extensions of scalars of a family of endomorphisms is invariant.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S' S : C} [MonObj R] [MonObj S'] [MonObj S] [IsCommMonObj R] [IsCommMonObj S']
  [IsCommMonObj S] (φ' : R ⟶ S') [IsMonHom φ'] (ψ : S' ⟶ S) [IsMonHom ψ] (φ : R ⟶ S)
  [IsMonHom φ] (h : φ' ≫ ψ = φ)

/-- The reduction of `S' ⊗ᴸ_R f ≫ s` is `S ⊗ᴸ_R f` followed by the reduction of `s`. -/
lemma derivedExtendScalarsReduction_map_comp {A B B' : DerivedCategory (Mod C R)} (f : B' ⟶ B)
    (s : (extendScalars φ').leftDerivedFunctor.obj B ⟶
      (extendScalars φ').leftDerivedFunctor.obj A) :
    derivedExtendScalarsReduction φ' ψ φ h ((extendScalars φ').leftDerivedFunctor.map f ≫ s) =
      (extendScalars φ).leftDerivedFunctor.map f ≫ derivedExtendScalarsReduction φ' ψ φ h s := by
  unfold derivedExtendScalarsReduction
  have hn := (derivedExtendScalarsCompIso φ' ψ φ h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, reassoc_of% hn, Category.assoc]

end CategoryTheory.Mod
