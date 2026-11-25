/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceShiftedRootProjectionTransportCore
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection

/-! # Shifted finite projections of an ordinary derived-limit cone

Source: diagonal tower trace proof (1), projection of the root cone.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem mapComplexNatTrans_commShift
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex α (.up ℤ)) ℤ where
  shift_comm n := by
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.id_comp, Category.comp_id]
    rfl

private theorem projected_unit_shift {B : Type u} [Category.{v} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (L : DiagonalRlim B) (n : ℕ) (P : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (j : ℤ) :
    (L.η.app P)⟦j⟧' ≫ (L.R.commShiftIso j).inv.app (DerivedCategory.Q.obj P) ≫
      (L.projection n).app ((DerivedCategory.Q.obj P)⟦j⟧) ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).commShiftIso j).hom.app
        (DerivedCategory.Q.obj P) =
      (L.η.app P ≫ (L.projection n).app (DerivedCategory.Q.obj P))⟦j⟧' := by
  let E := (evaluation ℕᵒᵖ B).obj (op n)
  let α := NatTrans.mapHomologicalComplex
    (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ B) ⥤ B) ⟶ E) (.up ℤ)
  let β := Functor.whiskerRight α DerivedCategory.Q ≫ E.mapDerivedCategoryFactors.inv
  have : NatTrans.CommShift α ℤ := mapComplexNatTrans_commShift _
  have : NatTrans.CommShift β ℤ := by dsimp only [β]; infer_instance
  have hb (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
      β.app K = L.η.app K ≫ (L.projection n).app (DerivedCategory.Q.obj K) := by
    apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app K)).mp
    simp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    exact (L.normalization K n).symm
  have h := shifted_normalized_unit DerivedCategory.Q
    ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    E.mapDerivedCategory L.R E.mapDerivedCategory β L.η (𝟙 E.mapDerivedCategory)
    (L.projection n) P j (by
      change β.app (P⟦j⟧) ≫ 𝟙 _ = _
      erw [Category.comp_id]
      exact hb (P⟦j⟧))
  have hh := congrArg (fun f ↦ f ≫ (E.mapDerivedCategory.commShiftIso j).hom.app
    (DerivedCategory.Q.obj P)) h
  simp only [NatTrans.id_app, Category.assoc, hb] at hh
  erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id] at hh
  exact hh.symm

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

/-- The normalized derived-limit projection of a shifted single tower is the
shift of its actual ordinary projection, with both exact endpoint comparisons.
Source: diagonal tower trace proof (1), the finite projection of the root cone.
(blueprint: lem-diagonal-local-shifted-limit-projection).
Proof: the natural transformation from the complexwise limit to evaluation
commutes with shifts, as checked componentwise. Normalize its factor through
the derived-limit unit on the shifted single complex. Shift compatibility of
that unit moves the shift comparison outside. The unshifted projection is the
single of the ordinary limit projection; applying the shift functor gives the
stated result. This treats one finite projection and does not assert that
finite evaluations detect arbitrary derived morphisms. -/
theorem local_shifted_limit_projection {B : Type u} [Category.{v} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] (L : DiagonalRlim B)
    (H : ℕᵒᵖ ⥤ B) (n : ℕ) (j : ℤ) :
    (diagonalOrdinaryRlim L H)⟦j⟧' ≫
      (L.R.commShiftIso j).inv.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
      (L.projection n).app (((DerivedCategory.singleFunctor _ 0).obj H)⟦j⟧) ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).commShiftIso j).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj H) ≫
      ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app H)⟦j⟧' =
    ((DerivedCategory.singleFunctor B 0).map (limit.π H (op n)))⟦j⟧' := by
  let P := (HomologicalComplex.single (ℕᵒᵖ ⥤ B) (.up ℤ) 0).obj H
  have h := projected_unit_shift L n P j
  have hp := ordinaryRlim_projection L H n
  simp only [diagonalOrdinaryRlim, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hp ⊢
  erw [L.R.map_id, Category.comp_id] at hp ⊢
  erw [(shiftFunctor (DerivedCategory B) j).map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% h]
  rw [← (shiftFunctor (DerivedCategory B) j).map_comp]
  rw [← (shiftFunctor (DerivedCategory B) j).map_comp]
  simpa only [P, DerivedCategory.Q_obj_single_obj, Category.assoc] using
    congrArg (fun f ↦ f⟦j⟧') hp

end AlgebraicGeometry.ProEtale.DiagonalTrace
