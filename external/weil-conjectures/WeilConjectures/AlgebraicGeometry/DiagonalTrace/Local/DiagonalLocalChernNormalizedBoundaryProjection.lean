/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalShiftedLimitProjection
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.Tactic.TransportExact

/-! # Finite integral coordinates for a strict Chern arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem shifted_cone_projection
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (U : C ⥤ B) (V : D ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : C) (N : D)
    (q : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) (n : ℕ) (j : ℤ) :
    shiftedComparison U.mapDerivedCategory (V.mapDerivedCategory ⋙ L.R)
        (exactConeComparison U V L M N q) j ≫
      (L.projection n).app _ ≫
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
        ((V.mapDerivedCategory.commShiftIso j).hom.app
          ((DerivedCategory.singleFunctor D 0).obj N)) ≫
      (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.commShiftIso j).hom.app _ ≫
      (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
          ((V.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app
          (V.obj N))⟦j⟧' =
    (U.mapDerivedCategory.commShiftIso j).hom.app _ ≫
      ((U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map (q.app (op n)))⟦j⟧' := by
  let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  simp only [shiftedComparison, exactConeComparison, Functor.map_comp,
    Functor.commShiftIso_comp_inv_app, Category.assoc]
  rw [L.R.commShiftIso_inv_naturality_assoc]
  rw [(L.projection n).naturality_assoc]
  rw [← E.map_comp_assoc, Iso.inv_hom_id_app]
  erw [E.map_id, Category.id_comp]
  rw [(L.projection n).naturality_assoc]
  rw [E.commShiftIso_hom_naturality_assoc]
  simp only [← (shiftFunctor (DerivedCategory B) j).map_comp]
  erw [← E.map_comp_assoc, Iso.inv_hom_id_app, E.map_id, Category.id_comp]
  erw [local_shifted_limit_projection L (V.obj N) n j]
  simp only [← (shiftFunctor (DerivedCategory B) j).map_comp,
    ← (DerivedCategory.singleFunctor B 0).map_comp, limit.lift_π]

private theorem normalized_cone_projection
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (U : C ⥤ B) (V : D ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M P : C) (N Q : D)
    (p : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N)
    (q : (Functor.const ℕᵒᵖ).obj (U.obj P) ⟶ V.obj Q)
    (f : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj P)⟦(2 : ℤ)⟧)
    (g : (DerivedCategory.singleFunctor D 0).obj N ⟶
      ((DerivedCategory.singleFunctor D 0).obj Q)⟦(2 : ℤ)⟧)
    (h : U.mapDerivedCategory.map f ≫
        shiftedComparison U.mapDerivedCategory (V.mapDerivedCategory ⋙ L.R)
          (exactConeComparison U V L P Q q) 2 =
      exactConeComparison U V L M N p ≫ L.R.map (V.mapDerivedCategory.map g)) (n : ℕ) :
    mapSingleArrow U 2 f ≫
        ((DerivedCategory.singleFunctor B 0).map (q.app (op n)))⟦(2 : ℤ)⟧' =
      (DerivedCategory.singleFunctor B 0).map (p.app (op n)) ≫
        mapSingleArrow (V ⋙ (evaluation ℕᵒᵖ B).obj (op n)) 2 g := by
  let E := (evaluation ℕᵒᵖ B).obj (op n)
  let ed := E.mapDerivedCategory
  let SQ := (DerivedCategory.singleFunctor D 0).obj Q
  have hh := congrArg (fun t ↦ (U.mapDerivedCategorySingleFunctor 0).inv.app M ≫
    t ≫ (L.projection n).app _ ≫
      ed.map ((V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app SQ) ≫
      (ed.commShiftIso (2 : ℤ)).hom.app _ ≫
      (ed.map ((V.mapDerivedCategorySingleFunctor 0).hom.app Q) ≫
        (E.mapDerivedCategorySingleFunctor 0).hom.app (V.obj Q))⟦(2 : ℤ)⟧') h
  have hg : ed.map (V.mapDerivedCategory.map g) ≫
      ed.map ((V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app SQ) ≫
      (ed.commShiftIso (2 : ℤ)).hom.app _ ≫
      (ed.map ((V.mapDerivedCategorySingleFunctor 0).hom.app Q) ≫
        (E.mapDerivedCategorySingleFunctor 0).hom.app (V.obj Q))⟦(2 : ℤ)⟧' =
    (ed.map ((V.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (E.mapDerivedCategorySingleFunctor 0).hom.app (V.obj N)) ≫
      mapSingleArrow E 2 (mapSingleArrow V 2 g) := by
    dsimp only [ed]
    simp only [mapSingleArrow, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    rw [E.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
    simp only [← E.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  simp only [Category.assoc] at hh
  erw [shifted_cone_projection U V L P Q q n 2] at hh
  erw [(L.projection n).naturality_assoc] at hh
  erw [hg] at hh
  simp only [Category.assoc] at hh
  rw [reassoc_of% (diagonalTrace_exactConeComparison_projection U V L M N p n)] at hh
  simp only [Iso.inv_hom_id_app_assoc] at hh
  rw [← mapSingleArrow_composite V E]
  simpa only [mapSingleArrow, Functor.map_comp, Category.assoc] using hh

private def completed_forget_iso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    diagonalCompletedRestriction l T ⋙ diagonalForget l T ≅
      DiagonalCoefficients.localCompletedForget l T :=
  NatIso.ofComponents (fun M ↦
    ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by ext U x; rfl, by ext U x; rfl⟩)
    (by intros M N f; ext U x; rfl)

/- The final step of `localChern_normalized_boundary_projection`, kept let-free and separate:
the definitions spell the derived category of `DiagonalAb T` as `Sheaf ..` and carry their own
abstracted proofs, so the identification is done by `transport_exact` (small congruence leaves)
instead of a kernel conversion under `Functor.map` projections. -/
private theorem completedIntegralProjection_eq_finiteConeChernClass
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (theta : unit T (Arings l (ULift.{u} (Padic l)) T) ⟶
      (line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧)
    (z : completedUnit l T ⟶ (completedLine l T)⟦(2 : ℤ)⟧)
    (h : (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (DiagonalCoefficients.localCompletedGenerator l T) ≫
        mapSingleArrow (DiagonalCoefficients.localCompletedForget l T) 2 z ≫
        (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (DiagonalCoefficients.localCompletedRoots l T).hom) ≫
        (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n))) ≫
        (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN)) =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n)) ≫
        (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (k.coefficientForget.inv.app (op n)) ≫
        mapSingleArrow (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
          diagonalForget l T) 2 theta ≫
        (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (k.lineForget.hom.app (op n))) ≫
        (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN))) :
    DiagonalCoefficients.completedIntegralProjection l T A n hA hN z =
      finiteConeChernClass l T c r k A n hA hN theta := by
  unfold DiagonalCoefficients.completedIntegralProjection finiteConeChernClass
  apply congrArg Ext.homEquiv.symm
  simp only [Functor.map_comp, Category.assoc]
  transport_exact h

/-- A whole-system normalization implies its integral finite coordinate equation.
This holds for every strict arrow, independently of Chern or Kummer normalization.
Source: diagonal tower trace proof (1), projection of the coefficient and root cones.
(blueprint: lem-diagonal-local-cone-integral-projection).

Proof: postcompose the normalization with the n-th derived-limit projection and the
exact evaluation/single comparisons. Naturality moves the strict arrow across the
projection. The exact-cone projection theorem computes the source cone. For the
shifted target cone, expand exactConeComparison, move the restriction/single
comparison across the projection, and use local_shifted_limit_projection. This
gives the single of k.lineProjection, with the exact shift comparisons in place.
Apply the exact scalar-forgetting functor and its single/shift naturality. The
line_projection field identifies the target with the actual root-limit projection.
The coefficient_projection field, followed by integerMap naturality for the ring
projection, identifies the source with the integer map into the finite ring followed
by coefficientForget inverse. Apply Ext.homEquiv.symm to this equation, then
postcompose with the canonical Cartier root map. The calculation works for zero
arrows, empty schemes, zero coefficient rings, and n=0 since n+1 is positive. -/
theorem localChern_normalized_boundary_projection
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (L : DiagonalRlim (DiagonalMod l T))
    (theta : unit T (Arings l (ULift.{u} (Padic l)) T) ⟶
      (line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧)
    (z : completedUnit l T ⟶ (completedLine l T)⟦(2 : ℤ)⟧)
    (hz : (diagonalCompletedUnderlying l T).map z ≫
        shiftedComparison (diagonalCompletedUnderlying l T)
          (r.F.mapDerivedCategory ⋙ L.R) (k.lineMap l (ULift.{u} (Padic l)) L) 2 =
      k.unitMap l (ULift.{u} (Padic l)) L ≫
        L.R.map (r.F.mapDerivedCategory.map theta)) :
    DiagonalCoefficients.completedIntegralProjection l T A n hA hN z =
      finiteConeChernClass l T c r k A n hA hN theta := by
  classical
  have hp := normalized_cone_projection (diagonalCompletedRestriction l T) r.F L
    (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l)))
    (Scheme.purTwistZlModule T l) _ _
    k.coefficientProjection k.lineProjection z theta hz n
  have hh := congrArg (mapSingleArrow (diagonalForget l T) (2 : ℤ)) hp
  simp only [mapSingleArrow_precompose, mapSingleArrow_postcompose,
    mapSingleArrow_composite] at hh
  have he := mapSingleArrow_natIso (DiagonalCoefficients.localCompletedForget l T)
    (diagonalCompletedRestriction l T ⋙ diagonalForget l T) (completed_forget_iso l T).symm
    (2 : ℤ) z
  have hq : (completed_forget_iso l T).inv.app (Scheme.purTwistZlModule T l) ≫
      (diagonalForget l T).map (k.lineProjection.app (op n)) ≫
      k.lineForget.hom.app (op n) =
    (DiagonalCoefficients.localCompletedRoots l T).hom ≫
      limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n) := by
    ext V x
    exact k.line_projection n V x
  have hc : (DiagonalCoefficients.localCompletedGenerator l T ≫
        (completed_forget_iso l T).inv.app
          (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l)))) ≫
        (diagonalForget l T).map (k.coefficientProjection.app (op n)) =
      diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n) := by
    apply (cancel_mono (k.coefficientForget.hom.app (op n))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hc0 : (completed_forget_iso l T).inv.app
          (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))) ≫
        (diagonalForget l T).map (k.coefficientProjection.app (op n)) ≫
        k.coefficientForget.hom.app (op n) =
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
            (Scheme.purTwistZlProjection T l n) := by
      ext V x
      exact k.coefficient_projection n V x
    rw [hc0]
    exact integerMap_naturality T (Scheme.purTwistZlProjection T l n)
  have hfinish := congrArg (fun f ↦
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (DiagonalCoefficients.localCompletedGenerator l T ≫
        (completed_forget_iso l T).inv.app
          (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l)))) ≫ f ≫
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (k.lineForget.hom.app (op n) ≫
      cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧') hh
  simp only [Category.assoc] at hfinish
  rw [← Functor.map_comp_assoc, hc] at hfinish
  simp only [Functor.map_comp, Category.assoc] at hfinish
  erw [reassoc_of% he] at hfinish
  simp only [← (shiftFunctor (DerivedCategory (DiagonalAb T)) (2 : ℤ)).map_comp,
    ← (DerivedCategory.singleFunctor (DiagonalAb T) 0).map_comp] at hfinish
  erw [reassoc_of% hq] at hfinish
  refine completedIntegralProjection_eq_finiteConeChernClass l T c r k A n hA hN theta z ?_
  simp only [CategoryTheory.Functor.assoc, Functor.map_comp] at hfinish
  clear hp hh he hq hc
  transport_exact hfinish

end AlgebraicGeometry.ProEtale.DiagonalTrace
