/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # Global augmentation sends cycles to total cycles

Source: Stacks Project, Tag 01FD, the left augmentation of the double complex. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction from global resolution sections gives a total cycle. No covering
or acyclicity assumption is required for this chain-map property.
Source: Stacks Project, Tag 01FD, the left augmentation of the double complex.
(blueprint: new-w2-additive-cech-alpha-representative)

Proof: The two restrictions of a global section to a pairwise intersection agree,
so its horizontal Cech differential is zero. Naturality of the resolution
differential identifies its vertical differential with the restriction of the
global differential, which is zero on cycles. The total differential is their
sum, with vertical sign +1 in horizontal degree zero. Lift through iCycles. -/
theorem additiveCech_alpha_representative
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (s : (additiveCechGlobal I).cycles n) :
    ∃ tα : (additiveCechTotal U I).cycles n,
      (additiveCechTotal U I).iCycles n tα =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) := by
  let K := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  let a (q : ℕ) : (additiveCechGlobal I).X q ⟶ (K.X 0).X q :=
    Pi.lift (fun y : Fin 1 → ι ↦ (I.cocomplex.X q).obj.map
      (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
        (Category.comp_id _) :
        (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
          Scheme.Etale.mk (𝟙 X)).op)
  have hh : a n ≫ (K.d 0 1).f n = 0 := by
    apply Pi.hom_ext
    intro y
    change Fin 2 → ι at y
    rw [Category.assoc, zero_comp]
    change a n ≫ ((cechComplexFunctor U).obj
      ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj)).d 0 1 ≫
        TopCat.Presheaf.cechComplexFunctorπ U
          ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj) 1 y = 0
    rw [TopCat.Presheaf.cechComplexFunctor_d_π]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    have he (j : Fin 2) : a n ≫ TopCat.Presheaf.cechComplexFunctorπ U
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj) 0
        (y ∘ j.succAbove) ≫
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj).map
          (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (j.succAbove l)).op =
        (I.cocomplex.X n).obj.map
          (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
            (Category.comp_id _) :
            (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
              Scheme.Etale.mk (𝟙 X)).op := by
      rw [← Category.assoc]
      change a n ≫ Pi.π _ _ ≫ _ = _
      dsimp only [a]
      erw [Pi.lift_comp_π_assoc]
      dsimp only [Functor.comp_map, Functor.op_map]
      erw [← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w _)
    simp_rw [he]
    simp [Fin.sum_univ_two]
  have hv : a n ≫ (K.X 0).d n (n + 1) =
      (additiveCechGlobal I).d n (n + 1) ≫ a (n + 1) := by
    apply Pi.hom_ext
    intro y
    change a n ≫ ((cechComplexFunctor U).map
      (Functor.whiskerLeft (additiveCechOpenInclusion X).op
        (I.cocomplex.d n (n + 1)).hom)).f 0 ≫ Pi.π _ y = _
    simp only [Category.assoc]
    erw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
    dsimp only [a]
    erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact (I.cocomplex.d n (n + 1)).hom.naturality _
  have hc : (additiveCechGlobal I).iCycles n ≫ additiveCechAlpha U I n ≫
      (additiveCechTotal U I).d n (n + 1) = 0 := by
    change (additiveCechGlobal I).iCycles n ≫ a n ≫
      K.ιTotal (.up ℕ) 0 n n (by simp) ≫ (K.total (.up ℕ)).d n (n + 1) = 0
    simp only [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [K.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      n (n + 1) (by simp [Nat.add_comm]), K.d₂_eq (.up ℕ) 0
      (by simp : (ComplexShape.up ℕ).Rel n (n + 1)) (n + 1) (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc, hh, zero_comp, comp_zero, zero_add]
    simp only [Category.assoc]
    rw [← Category.assoc (a n), hv]
    simp only [← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]
  let t := (additiveCechTotal U I).liftCycles
    ((additiveCechGlobal I).iCycles n ≫ additiveCechAlpha U I n)
    (n + 1) (by simp) hc
  refine ⟨t s, ?_⟩
  exact ConcreteCategory.congr_hom
    ((additiveCechTotal U I).liftCycles_i _ _ _ _) s

end AlgebraicGeometry.Scheme.Modules
