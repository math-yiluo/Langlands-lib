/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exact linear functors preserve normalized adic towers

Let `F : 𝒜 ⥤ ℬ` be an exact `R`-linear functor between `R`-linear abelian categories. Applying
`F` termwise to a normalized `ϖ`-adic tower of cochain complexes
(`CochainComplex.IsNormalizedAdicTower`) gives a normalized `ϖ`-adic tower:
`CochainComplex.IsNormalizedAdicTower.map`.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CochainComplex.IsNormalizedAdicTower

variable {R : Type*} [Ring R] {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
  [Linear R 𝒜] [Linear R ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] [F.Linear R] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- An exact functor sends a quasi-isomorphism `coker f ⟶ Y` of cochain complexes induced by
`g : X ⟶ Y` to a quasi-isomorphism `coker f' ⟶ F Y`, where `f'` is any morphism equal to the
image of `f`. -/
lemma quasiIso_cokernelDesc_map {X Y : CochainComplex 𝒜 ℤ} {f : X ⟶ X} {g : X ⟶ Y}
    {w : f ≫ g = 0} (hfg : QuasiIso (cokernel.desc f g w))
    {f' : (F.mapHomologicalComplex _).obj X ⟶ (F.mapHomologicalComplex _).obj X}
    (hf : (F.mapHomologicalComplex _).map f = f')
    {w' : f' ≫ (F.mapHomologicalComplex _).map g = 0} :
    QuasiIso (cokernel.desc f' ((F.mapHomologicalComplex _).map g) w') := by
  subst hf
  have : QuasiIso ((F.mapHomologicalComplex _).map (cokernel.desc f g w)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have h : cokernel.desc ((F.mapHomologicalComplex _).map f)
      ((F.mapHomologicalComplex _).map g) w' =
      (PreservesCokernel.iso (F.mapHomologicalComplex _) f).inv ≫
        (F.mapHomologicalComplex _).map (cokernel.desc f g w) := by
    refine coequalizer.hom_ext ?_
    rw [cokernel.π_desc, PreservesCokernel.iso_inv, π_comp_cokernelComparison_assoc,
      ← Functor.map_comp, cokernel.π_desc]
  rw [h]
  infer_instance

variable {F} in
/-- An exact `R`-linear functor, applied termwise, sends a normalized `ϖ`-adic tower of cochain
complexes to a normalized `ϖ`-adic tower. -/
lemma map {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (hT : IsNormalizedAdicTower ϖ T) :
    IsNormalizedAdicTower ϖ (T ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)) where
  smul_eq_zero n := by
    rw [Functor.comp_obj, ← CategoryTheory.Functor.map_id, ← Functor.map_smul,
      hT.smul_eq_zero, Functor.map_zero]
  quasiIso_cokernelDesc h := quasiIso_cokernelDesc_map F (hT.quasiIso_cokernelDesc h) (by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl)
  exact_smul a b := by
    refine ShortComplex.exact_of_iso ?_ ((hT.exact_smul a b).map (F.mapHomologicalComplex _))
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    all_goals
      simp only [ShortComplex.map_f, ShortComplex.map_g, Iso.refl_hom, Functor.map_smul,
        CategoryTheory.Functor.map_id]
      exact (id_comp _).trans (comp_id _).symm

end CochainComplex.IsNormalizedAdicTower
