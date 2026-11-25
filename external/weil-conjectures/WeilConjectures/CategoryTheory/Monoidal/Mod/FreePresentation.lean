/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Module objects as cokernels of free module objects

Let `C` be an abelian monoidal category and `A` a monoid object of `C` such that `A ⊗ -` is right
exact. Every `A`-module object `M` is the cokernel of a morphism of free `A`-modules
`A ⊗ K ⟶ A ⊗ M`, the counit `A ⊗ M ⟶ M` of the free-forgetful adjunction being an epimorphism
(`CategoryTheory.Mod.isColimitCounitCokernelCofork`). Consequently a natural transformation
between right exact functors on `Mod C A` is an isomorphism as soon as it is one on free modules
(`CategoryTheory.Mod.isIso_app_of_isIso_app_free`).
-/

@[expose] public section

namespace CategoryTheory.Mod

open MonoidalCategory MonObj Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] (A : C) [MonObj A] [Abelian C]
  [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft A)]

/-- The counit `A ⊗ M ⟶ M` of the free-forgetful adjunction is an epimorphism: its underlying
morphism is split by the unit. -/
instance epi_freeForgetAdjunction_counit_app (M : Mod C A) :
    Epi ((freeForgetAdjunction A).counit.app M) :=
  have : IsSplitEpi ((forget A).map ((freeForgetAdjunction A).counit.app M)) :=
    ⟨⟨(freeForgetAdjunction A).unit.app ((forget A).obj M),
      (freeForgetAdjunction A).right_triangle_components M⟩⟩
  (forget A).epi_of_epi_map inferInstance

/-- The presentation `A ⊗ K ⟶ A ⊗ M ⟶ M` of an `A`-module `M` by free modules, where `K` is the
kernel of the counit `A ⊗ M ⟶ M`. -/
noncomputable def freePresentation (M : Mod C A) :
    (free A).obj ((forget A).obj (kernel ((freeForgetAdjunction A).counit.app M))) ⟶
      (free A).obj ((forget A).obj M) :=
  (freeForgetAdjunction A).counit.app _ ≫ kernel.ι _

@[reassoc (attr := simp)]
lemma freePresentation_comp_counit (M : Mod C A) :
    freePresentation A M ≫ (freeForgetAdjunction A).counit.app M = 0 := by
  simp [freePresentation]

/-- Every `A`-module `M` is the cokernel of its presentation by free modules. -/
noncomputable def isColimitCounitCokernelCofork (M : Mod C A) :
    IsColimit (CokernelCofork.ofπ _ (freePresentation_comp_counit A M)) := by
  let S := ShortComplex.mk _ _ (freePresentation_comp_counit A M)
  have : Epi S.g := epi_freeForgetAdjunction_counit_app A M
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have : kernel.lift _ S.f S.zero = (freeForgetAdjunction A).counit.app _ := by
      rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
      rfl
    rw [this]
    infer_instance
  exact hS.gIsCokernel

/-- **Natural transformations between right exact functors are determined on free modules**: if
`κ : F ⟶ G` is an isomorphism on every free `A`-module, then it is an isomorphism, every module
being the cokernel of a morphism of free modules. -/
theorem isIso_app_of_isIso_app_free {D : Type*} [Category* D] [Abelian D]
    {F G : Mod C A ⥤ D} [PreservesFiniteColimits F] [PreservesFiniteColimits G] (κ : F ⟶ G)
    (h : ∀ X : C, IsIso (κ.app ((free A).obj X))) (M : Mod C A) : IsIso (κ.app M) := by
  let ε : (free A).obj ((forget A).obj M) ⟶ M := (freeForgetAdjunction A).counit.app M
  have := h ((forget A).obj M)
  have := h ((forget A).obj (kernel ((freeForgetAdjunction A).counit.app M)))
  let g := freePresentation A M
  have hF := CokernelCofork.mapIsColimit _ (isColimitCounitCokernelCofork A M) F
  have hG := CokernelCofork.mapIsColimit _ (isColimitCounitCokernelCofork A M) G
  have hnat : G.map g ≫ inv (κ.app _) = inv (κ.app _) ≫ F.map g := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← κ.naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hd : G.map g ≫ inv (κ.app _) ≫ F.map ε = 0 := by
    rw [reassoc_of% hnat, ← F.map_comp, freePresentation_comp_counit, F.map_zero,
      Limits.comp_zero]
  obtain ⟨d, hd'⟩ := CokernelCofork.IsColimit.desc' hG (inv (κ.app _) ≫ F.map ε) hd
  have hdε : G.map ε ≫ d = inv (κ.app _) ≫ F.map ε := hd'
  have extF {W : D} {a b : F.obj M ⟶ W} (hab : F.map ε ≫ a = F.map ε ≫ b) : a = b :=
    Cofork.IsColimit.hom_ext hF hab
  have extG {W : D} {a b : G.obj M ⟶ W} (hab : G.map ε ≫ a = G.map ε ≫ b) : a = b :=
    Cofork.IsColimit.hom_ext hG hab
  refine ⟨d, extF ?_, extG ?_⟩
  · rw [← Category.assoc, κ.naturality, Category.assoc, hdε, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  · rw [reassoc_of% hdε, κ.naturality, IsIso.inv_hom_id_assoc, Category.comp_id]


end CategoryTheory.Mod
