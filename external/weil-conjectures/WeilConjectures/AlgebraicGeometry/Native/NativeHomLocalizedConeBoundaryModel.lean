/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSignedShiftLaws
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import all WeilConjectures.AlgebraicGeometry.Native.NativeHomEvaluationShiftOne

/-! # The K-injective native Hom cone boundary

## References

* Stacks Project, Tags 08J9 and 08JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

open DerivedCategory

namespace AlgebraicGeometry.ProEtale

section Model
variable (C : Type d) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

private instance internalHom_additive : (MonoidalClosed.internalHom (C := C)).Additive where
  map_add := by
    intro X Y f g
    ext Z
    exact MonoidalClosed.pre_add_app f.unop g.unop Z

private instance internalHom_obj_additive (X : Cᵒᵖ) :
    (MonoidalClosed.internalHom.obj X).Additive :=
  inferInstanceAs (ihom X.unop).Additive

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem model_map {P P' : CochainComplex C ℤ} (f : P ⟶ P')
    (I : CochainComplex C ℤ) :
    CochainComplex.bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := I) f =
      CochainComplex.internalHomPre f I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.internalHomObj_hom_ext
  intro p q h
  change (CochainComplex.bifunctorHomMapLeft f).f n ≫
      CochainComplex.bifunctorHomπ MonoidalClosed.internalHom P I n p q h = _
  rw [CochainComplex.bifunctorHomMapLeft_f_π]
  exact (CochainComplex.internalHomPre_f_π f I n p q h).symm

private noncomputable def modelComparison (I : CochainComplex C ℤ) [I.IsKInjective] :
    (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp ≅
      Qh.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj I) := by
  refine NatIso.ofComponents
    (fun X ↦ asIso (qhInternalHomToIhom X.unop.as I)) ?_
  intro X Y f
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f.unop
  have hf : f = ((HomotopyCategory.quotient C (.up ℤ)).map g).op := by
    rw [hg]
    rfl
  subst f
  change Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.bifunctorHomMapLeft
        (H := MonoidalClosed.internalHom) (Y := I) g)) ≫ qhInternalHomToIhom P' I =
    qhInternalHomToIhom P I ≫ _
  rw [model_map C]
  exact qhInternalHomToIhom_naturality g I

end Model

/-- For a K-injective complex `I`, applying the internal Hom into `I` to the opposite of the
mapping-cone triangle of `f`, with the signed source component on the connecting arrow, gives a
distinguished triangle in the derived category. -/
theorem nativeHom_localized_cone_boundary_model
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G)
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    let M := DerivedCategory.Q.obj I
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
      (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁) ∈
        distTriang (DerivedCategory C) := by
  dsimp only
  let H := MonoidalClosed.internalHom.flip.obj (DerivedCategory.Q.obj I)
  let F := (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp
  obtain ⟨s, hs, hc⟩ :=
    CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact_coordinates
      MonoidalClosed.internalHom I
  let := s
  have : F.IsTriangulated := hs
  let e : F ≅ DerivedCategory.Qh.op ⋙ H := modelComparison C I
  let U := (triangleOpEquivalence (HomotopyCategory C (.up ℤ))).functor.obj
    (op (CochainComplex.mappingCone.triangleh f))
  have hU : U ∈ distTriang (HomotopyCategory C (.up ℤ))ᵒᵖ :=
    op_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
  have hd := F.map_distinguished U hU
  let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
    (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
  let V := Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
    (H.map T.mor₃ ≫ siteHomSignedSourceComponent (DerivedCategory.Q.obj I) 1 T.obj₁)
  have shiftQ (P : CochainComplex C ℤ) (n : ℤ) :
      DerivedCategory.Qh.map
          (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).hom.app P) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app
            ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
        (DerivedCategory.Q.commShiftIso n).hom.app P := by
    have h := NatTrans.shift_app_comm (DerivedCategory.quotientCompQhIso C).hom n P
    simp only [Functor.commShiftIso_comp_hom_app, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
    exact h
  have compat (P : CochainComplex C ℤ) :
      (F.commShiftIso (1 : ℤ)).inv.app
          (op ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
          e.hom.app ((op ((HomotopyCategory.quotient C (.up ℤ)).obj P))⟦(1 : ℤ)⟧) ≫
          H.map ((DerivedCategory.Qh.op.commShiftIso (1 : ℤ)).hom.app
            (op ((HomotopyCategory.quotient C (.up ℤ)).obj P))) ≫
          siteHomSignedSourceComponent (DerivedCategory.Q.obj I) 1
            (op (DerivedCategory.Q.obj P)) =
        (e.hom.app (op ((HomotopyCategory.quotient C (.up ℤ)).obj P)))⟦(1 : ℤ)⟧' := by
    obtain ⟨σ, hσ, hσ'⟩ := hc P
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
      Quotient.lift.isLift_inv] at hσ'
    erw [(shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id,
      Category.id_comp, Category.comp_id] at hσ'
    let τ := ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso (-1 : ℤ)).hom.app P
    have hτ : (DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P ≫
          DerivedCategory.Qh.map τ =
        (DerivedCategory.Qh.commShiftIso (-1 : ℤ)).inv.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
      apply (cancel_mono ((DerivedCategory.Qh.commShiftIso (-1 : ℤ)).hom.app _)).mp
      dsimp only [τ]
      erw [Category.assoc, shiftQ, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
      rfl
    have hmap : H.map ((DerivedCategory.Qh.op.commShiftIso (1 : ℤ)).hom.app
          (op ((HomotopyCategory.quotient C (.up ℤ)).obj P))) =
        H.map (DerivedCategory.Qh.op.map
          ((shiftFunctorOpIso (HomotopyCategory C (.up ℤ)) 1 (-1)
            (by omega)).hom.app (op ((HomotopyCategory.quotient C (.up ℤ)).obj P)))) ≫
          H.map (DerivedCategory.Qh.map τ).op ≫
          H.map ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P).op ≫
          H.map ((shiftFunctorOpIso (DerivedCategory C) 1 (-1) (by omega)).inv.app
            (op (DerivedCategory.Q.obj P))) := by
      rw [Functor.op_commShiftIso_hom_app _ _ 1 (-1) (by omega)]
      rw [← hτ]
      simp only [Functor.op_map, op_comp, H.map_comp, Category.assoc]
      rfl
    rw [hmap]
    simp only [Category.assoc]
    erw [← e.hom.naturality_assoc, ← e.hom.naturality_assoc]
    simp only [← Category.assoc]
    simp only [← Category.assoc] at hσ'
    erw [hσ']
    simp only [Category.assoc]
    change (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app _ ≫
      DerivedCategory.Q.map σ ≫ DerivedCategory.qhInternalHomToIhom (P⟦(-1 : ℤ)⟧) I ≫
      H.map ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P).op ≫
      H.map ((shiftFunctorOpIso (DerivedCategory C) 1 (-1) (by omega)).inv.app
        (op (DerivedCategory.Q.obj P))) ≫
      siteHomSignedSourceComponent (DerivedCategory.Q.obj I) 1
        (op (DerivedCategory.Q.obj P)) = (DerivedCategory.qhInternalHomToIhom P I)⟦(1 : ℤ)⟧'
    have hev := nativeHom_evaluation_shift_one P I σ hσ
    rw [reassoc_of% nativeHom_comparison_transport (P⟦(-1 : ℤ)⟧) I,
      nativeHom_comparison_transport P I] at hev
    rw [hev]
    erw [Iso.inv_hom_id_app_assoc]
  let j₀ : DerivedCategory.Qh.mapTriangle.obj
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingCone.triangle f)) ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f) :=
    (Functor.mapTriangleCompIso (HomotopyCategory.quotient C (.up ℤ))
      DerivedCategory.Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).app _
  let j : T ≅ DerivedCategory.Qh.op.mapTriangle.obj U :=
    (triangleOpEquivalence (DerivedCategory C)).functor.mapIso j₀.op ≪≫
      DerivedCategory.Qh.mapTriangleOpCompTriangleOpEquivalenceFunctorApp _
  have hT₃ : T.mor₃ = (DerivedCategory.Qh.op.mapTriangle.obj U).mor₃ := by
    have hj := j.hom.comm₃
    simp only [Functor.mapTriangle_obj, Functor.op_obj, Functor.op_map, Triangle.mk_obj₁,
      triangleOpEquivalence_functor, TriangleOpEquivalence.functor,
      opShiftFunctorEquivalence_inverse, opShiftFunctorEquivalence_functor, Functor.comp_obj,
      CochainComplex.mappingCone.triangle_obj₁, CochainComplex.mappingCone.triangle_obj₂,
      CochainComplex.mappingCone.triangle_obj₃, CochainComplex.mappingCone.triangle_mor₁,
      CochainComplex.mappingCone.triangle_mor₂, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, op_comp, Functor.comp_map,
      Functor.mapTriangleCompIso, Functor.mapTriangleIso, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, NatIso.ofComponents.app, Iso.op_trans,
      Functor.mapIso_trans, Iso.trans_assoc, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
      Triangle.isoMk_hom, Iso.app_hom, Quotient.lift.isLift_hom, Quiver.Hom.unop_op,
      Triangle.homMk_hom₃, Triangle.homMk_hom₂, Triangle.homMk_hom₁, Iso.symm_hom,
      NatIso.ofComponents_inv_app, Triangle.isoMk_inv, Iso.refl_inv, op_id,
      triangleCategory_comp, TriangleMorphism.comp_hom₁,
      Functor.mapTriangleOpCompTriangleOpEquivalenceFunctorApp_hom_hom₁, Category.comp_id,
      TriangleMorphism.comp_hom₃,
      Functor.mapTriangleOpCompTriangleOpEquivalenceFunctorApp_hom_hom₃, j, j₀] at hj
    erw [op_id, CategoryTheory.Functor.map_id, Category.comp_id, op_id,
      Category.id_comp] at hj
    exact hj
  have eT : F.mapTriangle.obj U ≅ V := by
    refine Triangle.isoMk _ _ (asIso (DerivedCategory.qhInternalHomToIhom
      (CochainComplex.mappingCone f) I))
      (asIso (DerivedCategory.qhInternalHomToIhom G I))
      (asIso (DerivedCategory.qhInternalHomToIhom E I)) ?_ ?_ ?_
    · exact e.hom.naturality U.mor₁
    · exact e.hom.naturality U.mor₂
    · change (F.map U.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app U.obj₁) ≫
        (DerivedCategory.qhInternalHomToIhom (CochainComplex.mappingCone f) I)⟦(1 : ℤ)⟧' =
          DerivedCategory.qhInternalHomToIhom E I ≫ H.map T.mor₃ ≫
            siteHomSignedSourceComponent (DerivedCategory.Q.obj I) 1 T.obj₁
      simp only [Category.assoc]
      have h := compat (CochainComplex.mappingCone f)
      have h' := congrArg (fun z ↦ (F.commShiftIso (1 : ℤ)).hom.app U.obj₁ ≫ z) h
      simp only [← Category.assoc] at h'
      erw [Iso.hom_inv_id_app, Category.id_comp] at h'
      erw [← h']
      simp only [Category.assoc]
      erw [e.hom.naturality_assoc]
      simp only [Functor.comp_map]
      erw [← H.map_comp_assoc, hT₃]
      rfl
  exact isomorphic_distinguished _ hd _ eT.symm

end AlgebraicGeometry.ProEtale
