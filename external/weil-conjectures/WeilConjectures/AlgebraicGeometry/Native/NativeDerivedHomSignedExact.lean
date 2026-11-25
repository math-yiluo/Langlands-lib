/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSignedShiftLaws
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.AlgebraicGeometry.Native.NativeHomLocalizedConeBoundary
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Signed exactness of the native derived internal Hom

## References

* Stacks Project, Tags 08J9 and 08JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale

private theorem rightAdjointUniq_ofNatIsoLeft
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L' ≅ L) :
    (a.rightAdjointUniq (b.ofNatIsoLeft e)).hom =
      conjugateEquiv a b e.hom := by
  ext X
  simp [Adjunction.rightAdjointUniq, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit, Category.assoc]

section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

private def leftShiftMateIso (K : D) (n : ℤ) :
    (shiftEquiv D n).functor ⋙ tensorLeft K ≅ tensorLeft (K⟦n⟧) :=
  (tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm

omit [MonoidalClosed D] in
private theorem leftShiftMateIso_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    Functor.whiskerLeft (shiftEquiv D n).functor ((tensoringLeft D).map f) ≫
        (leftShiftMateIso L n).hom =
      (leftShiftMateIso K n).hom ≫ (tensoringLeft D).map (f⟦n⟧') := by
  ext M
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, leftShiftMateIso,
    Iso.trans_hom, Iso.symm_hom]
  change ((curriedTensor D).map f).app (M⟦n⟧) ≫
      (((curriedTensor D).obj L).commShiftIso n).hom.app M ≫
        (siteHomTensorParameterShift L n).inv.app M =
    ((((curriedTensor D).obj K).commShiftIso n).hom.app M ≫
      (siteHomTensorParameterShift K n).inv.app M) ≫
        ((curriedTensor D).map (f⟦n⟧')).app M
  rw [← Category.assoc, ← NatTrans.shift_app_comm ((curriedTensor D).map f) n M,
    Category.assoc]
  simpa only [siteHomTensorParameterShift, NatIso.ofComponents_inv_app,
    Iso.app_inv, Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app,
    Category.assoc] using
    congrArg (fun z ↦ ((tensorLeft K).commShiftIso n).hom.app M ≫ z)
      ((((curriedTensor D).flip.obj M).commShiftIso n).inv.naturality f)

private theorem siteHomSourceShift_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    pre (f⟦n⟧') ≫ (siteHomSourceShift K n).hom =
      (siteHomSourceShift L n).hom ≫ Functor.whiskerRight (pre f) (shiftFunctor D (-n)) := by
  have hs (K : D) : (siteHomSourceShift K n).hom =
      conjugateEquiv (ihom.adjunction (K⟦n⟧))
        ((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K))
        (leftShiftMateIso K n).hom := by
    unfold siteHomSourceShift
    exact rightAdjointUniq_ofNatIsoLeft _ _ _
  rw [hs K, hs L]
  unfold pre
  change _ = _ ≫ Functor.whiskerRight
    (conjugateEquiv (ihom.adjunction L) (ihom.adjunction K)
      ((tensoringLeft D).map f)) (shiftEquiv D n).inverse
  rw [← conjugateEquiv_whiskerLeft (ihom.adjunction L)
    (ihom.adjunction K) (shiftEquiv D n).toAdjunction]
  calc
    _ = conjugateEquiv _ _
        ((leftShiftMateIso K n).hom ≫ (tensoringLeft D).map (f⟦n⟧')) :=
      conjugateEquiv_comp _ _ _ _ _
    _ = conjugateEquiv _ _
        (Functor.whiskerLeft (shiftEquiv D n).functor ((tensoringLeft D).map f) ≫
          (leftShiftMateIso L n).hom) :=
      congrArg _ (leftShiftMateIso_naturality f n).symm
    _ = _ := (conjugateEquiv_comp _ _ _ _ _).symm

omit [Preadditive D] [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int] in
private theorem shiftEquality_naturality (a b : ℤ) (h : a = b)
    {A B : D} (f : A ⟶ B) :
    f⟦a⟧' ≫ (eqToIso (congrArg (shiftFunctor D) h)).hom.app B =
      (eqToIso (congrArg (shiftFunctor D) h)).hom.app A ≫ f⟦b⟧' := by
  subst b
  simp

private theorem oppositeSource_naturality {K L : D} (f : K ⟶ L) (n : ℤ) :
    pre (f⟦-n⟧') ≫ (siteHomOppositeSourceShift K n).hom =
      (siteHomOppositeSourceShift L n).hom ≫
        Functor.whiskerRight (pre f) (shiftFunctor D n) := by
  ext M
  have h := congr_app (siteHomSourceShift_naturality f (-n)) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  simp only [siteHomOppositeSourceShift, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, h, Category.assoc,
    shiftEquality_naturality (- -n) n (neg_neg n) ((pre f).app M), Category.assoc]

private theorem signedSource_naturality (M : D) (n : ℤ)
    (X Y : Dᵒᵖ) (f : X ⟶ Y) :
    let H := internalHom.flip.obj M
    H.map (f⟦n⟧') ≫ siteHomSignedSourceComponent M n Y =
      siteHomSignedSourceComponent M n X ≫ (H.map f)⟦n⟧' := by
  have h := congr_app (oppositeSource_naturality f.unop n) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  dsimp only [siteHomSignedSourceComponent]
  change (pre (f.unop⟦-n⟧')).app M ≫ _ =
    _ ≫ ((pre f.unop).app M)⟦n⟧'
  simpa only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Units.smul_def] using congrArg (fun z ↦ (n * (n + 1) / 2).negOnePow • z) h

variable [MonoidalPreadditive D]

private def signedSourceIso (M : D) (n : ℤ) :
    shiftFunctor Dᵒᵖ n ⋙ MonoidalClosed.internalHom.flip.obj M ≅
      MonoidalClosed.internalHom.flip.obj M ⋙ shiftFunctor D n :=
  NatIso.ofComponents
    (fun X ↦ (n * (n + 1) / 2).negOnePow •
      (siteHomOppositeSourceShift X.unop n).app M)
    (fun {X Y} f ↦ signedSource_naturality M n X Y f)

@[instance_reducible] private def signedSourceCommShift (M : D) :
    (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ where
  commShiftIso := signedSourceIso M
  commShiftIso_zero := by
    apply Iso.ext
    ext X
    exact (siteHom_signed_source_shift_laws M).1 X
  commShiftIso_add m n := by
    apply Iso.ext
    ext X
    simpa only [Functor.CommShift.isoAdd_hom_app, signedSourceIso,
      NatIso.ofComponents_hom_app, Preadditive.smul_iso_hom, Iso.app_hom,
      siteHomSignedSourceComponent] using
      (siteHom_signed_source_shift_laws M).2 m n X

end Shift

/-- Native derived internal Hom has the signed exact contravariant structure. -/
theorem nativeDerivedHom_signed_exact
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (M : DerivedCategory C) :
    let H := MonoidalClosed.internalHom.flip.obj M
    ∃ s : H.CommShift ℤ,
      (fun [_s : H.CommShift ℤ] ↦ H.IsTriangulated ∧
        ∀ (K : DerivedCategory C) (n : ℤ),
          (H.commShiftIso n).hom.app (op K) =
            (n * (n + 1) / 2).negOnePow •
              (siteHomOppositeSourceShift K n).hom.app M) (_s := s) := by
  dsimp only
  let H := MonoidalClosed.internalHom.flip.obj M
  let : H.CommShift ℤ := signedSourceCommShift M
  refine ⟨inferInstance, ?_, ?_⟩
  · constructor
    intro T hT
    obtain ⟨T', hT', ⟨e⟩⟩ := (mem_distTriang_op_iff' T).1 hT
    obtain ⟨E, G, f, ⟨e'⟩⟩ := (DerivedCategory.mem_distTriang_iff T').1 hT'
    have e'' : T ≅ (triangleOpEquivalence (DerivedCategory C)).functor.obj
        (op (DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.mappingCone.triangle f))) :=
      e ≪≫ (triangleOpEquivalence (DerivedCategory C)).functor.mapIso e'.op.symm
    apply Pretriangulated.isomorphic_distinguished _
      (nativeHom_localized_cone_boundary f M) _ (H.mapTriangle.mapIso e'')
  · intro K n
    rfl

end AlgebraicGeometry.ProEtale
