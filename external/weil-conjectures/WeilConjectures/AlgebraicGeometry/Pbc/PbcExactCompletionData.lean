/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement

import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

/-! # Exact completion from the actual reflector. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme

private theorem reflectiveUnitLocus
    {C : Type*} [Category C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (F : C ⥤ C) [F.CommShift ℤ]
    (η : 𝟭 C ⟶ F) [NatTrans.CommShift η ℤ]
    (hP : ∀ X, P X ↔ IsIso (η.app X))
    (hF : ∀ X, P (F.obj X))
    (hu : ∀ X Y, P Y →
      Function.Bijective (fun f : F.obj X ⟶ Y ↦ η.app X ≫ f)) :
    P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated := by
  have hiso : P.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    have : IsIso (η.app X) := (hP X).1 hX
    apply (hP Y).2
    have h : η.app Y = e.inv ≫ η.app X ≫ F.map e.hom := by
      simpa using congrArg (fun f ↦ e.inv ≫ f) (η.naturality e.hom)
    rw [h]
    infer_instance⟩
  have := hiso
  have hs : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    have : IsIso (η.app X) := (hP X).1 hX
    apply (hP _).2
    rw [NatTrans.app_shift η n X]
    infer_instance⟩⟩
  have := hs
  have heq : P = P.leftOrthogonal.rightOrthogonal := by
    funext X
    apply propext
    refine ⟨fun hX Y f hY ↦ hY f hX, fun hX ↦ ?_⟩
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle (η.app X)
    let T := Triangle.mk (η.app X) g h
    have hz : P.leftOrthogonal Z := by
      intro Y f hY
      have hgf : g ≫ f = 0 := (hu X Y hY).1 (by
        simpa [T, Category.assoc] using
          congrArg (fun k ↦ k ≫ f) (Pretriangulated.comp_distTriang_mor_zero₁₂ T hT))
      obtain ⟨k, hk⟩ := Pretriangulated.Triangle.yoneda_exact₃ T hT f hgf
      obtain ⟨k', hk'⟩ := (hu (X⟦(1 : ℤ)⟧) Y hY).2 k
      have hk'' : k = (η.app X)⟦(1 : ℤ)⟧' ≫
          (F.commShiftIso (1 : ℤ)).inv.app X ≫ k' := by
        rw [← hk', NatTrans.app_shift η (1 : ℤ) X]
        simp
      rw [hk, hk'']
      have hz := Pretriangulated.comp_distTriang_mor_zero₃₁ T hT
      simpa [T, Category.assoc] using
        congrArg (fun k ↦ k ≫ (F.commShiftIso (1 : ℤ)).inv.app X ≫ k') hz
    have hxs : P.leftOrthogonal.rightOrthogonal (X⟦(1 : ℤ)⟧) :=
      P.leftOrthogonal.rightOrthogonal.le_shift (1 : ℤ) X hX
    have hh : h = 0 := hxs h hz
    obtain ⟨k, hk⟩ := Pretriangulated.Triangle.coyoneda_exact₃ T hT (𝟙 Z) (by
      simpa [T] using hh)
    have hid : 𝟙 Z = 0 := by
      simpa only [hz k (hF X), Limits.zero_comp] using hk
    exact (hP X).2 ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).1
      ((Limits.IsZero.iff_id_eq_zero Z).2 hid))
  refine ⟨hiso, ?_⟩
  rw [heq]
  infer_instance

/-- The actual completion reflector gives an exact pointed functor, and its
unit detects intrinsic completeness in the actual coefficient presentation. -/
theorem pbcExactCompletionData (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ (F : PbcCompletedDerived T d ⥤ PbcCompletedDerived T d)
      (η : 𝟭 _ ⟶ F) (_ : F.Additive) (_ : F.CommShift ℤ)
      (_ : F.IsTriangulated) (_ : NatTrans.CommShift η ℤ),
      ∀ K, PbcIsIntrinsicallyComplete T d K ↔ IsIso (η.app K)  := by
  let P : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let L := P.ι.leftAdjoint
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let F := pbcActualCompletion d T
  let η := pbcActualCompletionUnit d T
  have hη : NatTrans.CommShift η ℤ := (pbcActualCompletionShift_exists d T).exists.choose_spec
  have := hη
  have hiso : P.IsClosedUnderIsomorphisms := ⟨by
    rintro X Y e ⟨r, f, hf, C, eC, hC⟩
    refine ⟨r, f, hf, C,
      eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison T d).inv).mapIso e, ?_⟩
    change IsIso (_ ≫ _)
    dsimp only [Iso.trans_inv, Functor.mapIso_inv]
    rw [Category.assoc]
    have : IsIso (completedIntrinsicCompletionMap T
        { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
          quotientFinite := d.quotientFinite } r f C eC) := hC
    change IsIso ((pbcDerivedExtend (pbcCompletedComparison T d).inv).map e.inv ≫
      completedIntrinsicCompletionMap T
        { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
          quotientFinite := d.quotientFinite } r f C eC)
    infer_instance⟩
  have := hiso
  have hp (X) : P X ↔ IsIso (η.app X) := by
    change P X ↔ IsIso (adj.unit.app X)
    rw [adj.isIso_unit_app_iff_mem_essImage]
    refine ⟨fun h ↦ ⟨⟨X, h⟩, ⟨Iso.refl _⟩⟩, ?_⟩
    rintro ⟨Y, ⟨e⟩⟩
    exact P.prop_of_iso e Y.property
  have hF (X) : P (F.obj X) := (L.obj X).property
  have hu (X Y) (hY : P Y) :
      Function.Bijective (fun f : F.obj X ⟶ Y ↦ η.app X ≫ f) := by
    constructor
    · intro f g h
      have he : (ObjectProperty.homMk f : L.obj X ⟶ ⟨Y, hY⟩) =
          ObjectProperty.homMk g := (adj.homEquiv X ⟨Y, hY⟩).injective h
      exact congrArg (fun k ↦ k.hom) he
    · intro f
      exact ⟨((adj.homEquiv X ⟨Y, hY⟩).symm f).hom,
        (adj.homEquiv X ⟨Y, hY⟩).apply_symm_apply f⟩
  have htri := (reflectiveUnitLocus P F η hp hF hu).2
  have := htri
  let : L.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : L.IsTriangulated := adj.isTriangulated_leftAdjoint
  have : L.Additive := adj.left_adjoint_additive
  let F' := L ⋙ P.ι
  let η' : 𝟭 _ ⟶ F' := adj.unit
  have : NatTrans.CommShift η' ℤ := inferInstanceAs (NatTrans.CommShift adj.unit ℤ)
  exact ⟨F', η', inferInstance, inferInstance, inferInstance, inferInstance, hp⟩

end AlgebraicGeometry.Scheme
