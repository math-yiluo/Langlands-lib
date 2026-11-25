/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSingleTensorLax
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
import all WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
/-! # The unit law for the specified derived single tensorator

Source: the degree-zero realization of the affine-space supported product.
(blueprint: lem-pur-coordinate-single-tensor-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem unit_of_inverse {C : Type*} [Category C] [MonoidalCategory C]
    {M N : C} (e : M ≅ 𝟙_ C) (ε : 𝟙_ C ⟶ M) (μ : M ⊗ N ⟶ N)
    (hε : ε ≫ e.hom = 𝟙 _) (hμ : (λ_ N).hom = ε ▷ N ≫ μ) :
    μ = e.hom ▷ N ≫ (λ_ N).hom := by
  have h : ε = e.inv := (Iso.comp_hom_eq_id _).mp hε
  rw [h] at hμ
  rw [hμ, ← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp]

private theorem unit_transport_inverse {C : Type*} [Category C]
    {I J W V U : C} (e : U ≅ V) (j : W ≅ V) (q : J ≅ W) (z : I ≅ J)
    (ε : I ⟶ V) (h : ε = z.hom ≫ q.hom ≫ j.hom) :
    (ε ≫ e.inv) ≫ (e.hom ≫ j.inv ≫ q.inv ≫ z.inv) = 𝟙 I := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id]

private theorem unit_map_eq_id {C : Type*} [Category C] [MonoidalCategory C]
    (ε : 𝟙_ C ⟶ 𝟙_ C) (μ : 𝟙_ C ⊗ 𝟙_ C ⟶ 𝟙_ C)
    (h : ε ▷ (𝟙_ C) ≫ μ = (λ_ (𝟙_ C)).hom) (hμ : μ = (λ_ (𝟙_ C)).hom) :
    ε = 𝟙 _ := by
  apply whiskerRight_injective_of_tensorIso (ρ_ (𝟙_ C))
  apply (cancel_mono (λ_ (𝟙_ C)).hom).mp
  simpa only [hμ, id_whiskerRight, Category.id_comp] using h

private theorem single_left_unitor
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C] (M : C) :
    cupSingleTensorMap (𝟙_ C) M ≫ (DerivedCategory.singleFunctor C 0).map (λ_ M).hom =
      (DerivedCategory.singleFunctorObjUnitIso C).hom ▷
        (DerivedCategory.singleFunctor C 0).obj M ≫
          (λ_ ((DerivedCategory.singleFunctor C 0).obj M)).hom := by
  obtain ⟨ms, hms⟩ := Etale.exists_singleCochainMonoidal (C := C)
  let : (CochainComplex.singleFunctor C 0).Monoidal := ms
  let e := DerivedCategory.singleFunctorIsoCompQ C 0
  let m := Functor.LaxMonoidal.transport e.symm
  let := m
  have hμ (L M : C) : Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor C 0) L M =
      cupSingleTensorMap L M := by
    rw [Functor.LaxMonoidal.transport_μ e.symm]
    simp only [Functor.LaxMonoidal.comp_μ]
    have hm : Functor.LaxMonoidal.μ (CochainComplex.singleFunctor C 0) L M =
        (Etale.singleCochainTensorIso L M).hom := hms L M
    rw [hm]
    simp only [cupSingleTensorMap, Etale.singleCochainTensorIso, Iso.symm_inv,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
      Category.assoc, tensorIso_hom, e]
    rfl
  have hs : Functor.LaxMonoidal.ε (CochainComplex.singleFunctor C 0) =
      𝟙 (𝟙_ (CochainComplex C ℤ)) := by
    have hc : (Etale.singleCochainTensorIso (𝟙_ C) (𝟙_ C)).hom ≫
        (CochainComplex.singleFunctor C 0).map (λ_ (𝟙_ C)).hom =
          (λ_ ((CochainComplex.singleFunctor C 0).obj (𝟙_ C))).hom :=
      congrArg Iso.hom (Etale.singleCochainTensorIso_leftUnitor (𝟙_ C))
    apply unit_map_eq_id _
      ((Etale.singleCochainTensorIso (𝟙_ C) (𝟙_ C)).hom ≫
        (CochainComplex.singleFunctor C 0).map (λ_ (𝟙_ C)).hom) _ hc
    have hu := Functor.LaxMonoidal.left_unitality (CochainComplex.singleFunctor C 0)
      (𝟙_ C)
    have hm : Functor.LaxMonoidal.μ (CochainComplex.singleFunctor C 0)
        (𝟙_ C) (𝟙_ C) =
          (Etale.singleCochainTensorIso (𝟙_ C) (𝟙_ C)).hom := hms _ _
    rw [hm] at hu
    exact hu.symm
  have hQ : Functor.LaxMonoidal.ε (DerivedCategory.Q (C := C)) =
      Functor.LaxMonoidal.ε DerivedCategory.Qh ≫
        DerivedCategory.Qh.map (Functor.LaxMonoidal.ε
          (HomotopyCategory.quotient C (.up ℤ))) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app _ := by
    change (_ ≫ _) ≫ _ = _
    rw [Category.assoc]
  have hσ : Functor.LaxMonoidal.ε
      (CochainComplex.singleFunctor C 0 ⋙ DerivedCategory.Q) =
        Functor.LaxMonoidal.ε (DerivedCategory.Q (C := C)) := by
    change Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.ε (CochainComplex.singleFunctor C 0)) = _
    rw [hs]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  have hε : Functor.LaxMonoidal.ε (DerivedCategory.singleFunctor C 0) ≫
      (DerivedCategory.singleFunctorObjUnitIso C).hom = 𝟙 _ := by
    rw [Functor.LaxMonoidal.transport_ε e.symm, hσ]
    unfold DerivedCategory.singleFunctorObjUnitIso
    exact unit_transport_inverse
      (e.app (𝟙_ C))
      ((DerivedCategory.quotientCompQhIso C).app
        ((CochainComplex.singleFunctor C 0).obj (𝟙_ C)))
      (DerivedCategory.Qh.mapIso
        (Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ))))
      (asIso (Functor.LaxMonoidal.ε DerivedCategory.Qh)) _ hQ
  have hu := Functor.LaxMonoidal.left_unitality (DerivedCategory.singleFunctor C 0) M
  rw [hμ] at hu
  exact unit_of_inverse (DerivedCategory.singleFunctorObjUnitIso C) _ _ hε hu

/-- The specified single tensor comparison carries a supplied coefficient-unit
isomorphism to its canonical derived left unitor.

Source: the empty factor in the affine-space supported-product construction.
(blueprint: lem-pur-coordinate-single-tensor-unit).

Proof: transport the monoidal single-cochain functor through the quotient comparison.
Its tensorator is the specified cupSingleTensorMap. The cochain left-unit equation
identifies its unit map with the identity; the localization unit factors through Qh
and the homotopy quotient, whose inverses are precisely singleFunctorObjUnitIso.
The lax left-unit axiom therefore gives the derived single left-unit equation.
Finally apply tensorator naturality to the given coefficient-unit isomorphism. -/
theorem coordinate_single_tensor_unit
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C] {L : C} (N : C) (e : L ≅ 𝟙_ C) :
    cupSingleTensorMap L N ≫ (DerivedCategory.singleFunctor C 0).map
        (e.hom ▷ N ≫ (λ_ N).hom) =
      ((DerivedCategory.singleFunctor C 0).mapIso e ≪≫
          DerivedCategory.singleFunctorObjUnitIso C).hom ▷
        (DerivedCategory.singleFunctor C 0).obj N ≫
          (λ_ ((DerivedCategory.singleFunctor C 0).obj N)).hom := by
  obtain ⟨m, hm⟩ := coordinate_single_tensor_lax (C := C)
  let := m
  have hn := Functor.LaxMonoidal.μ_natural (DerivedCategory.singleFunctor C 0)
    e.hom (𝟙 N)
  rw [hm, hm] at hn
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hn
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc, single_left_unitor]
  simp only [Iso.trans_hom, Functor.mapIso_hom, comp_whiskerRight, Category.assoc]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
