/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback

/-! # Completed pullback preserves shifts and distinguished triangles
Source: literature/stacks-project/proetale.tex, Tag 099N (2),(5), with
`derived.tex`, Tag 05SE, and `sites-cohomology.tex`, Tag 0941
(blueprint: lem-cbc-completed-pullback-triangles).

The specified strict-tower completed pullback has coherent shift comparisons,
and it carries distinguished triangles whose vertices are intrinsically derived
complete to distinguished image triangles.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
variable (d : AdicCoefficientDatum A)

private theorem reflective_triangulated {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : ObjectProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
    [F.CommShift ℤ] [NatTrans.CommShift η ℤ]
    (hout : ∀ X, P (F.obj X))
    (hfix : ∀ X, P X ↔ IsIso (η.app X))
    (href : ∀ X L, P L → Function.Bijective (fun f : F.obj X ⟶ L ↦ η.app X ≫ f)) :
    P.IsTriangulated := by
  have hshift (X : C) (n : ℤ) :
      (η.app X)⟦n⟧' = η.app (X⟦n⟧) ≫ (F.commShiftIso n).hom.app X := by
    simpa using NatTrans.shift_app_comm η n X
  have : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro X hX
    apply (hfix _).mpr
    have := (hfix X).mp hX
    rw [NatTrans.app_shift η n X]
    infer_instance
  have hle : P ≤ P.leftOrthogonal.rightOrthogonal := fun _ hX _ f hL ↦ hL f hX
  have heq : P = P.leftOrthogonal.rightOrthogonal := by
    apply le_antisymm hle
    intro X hX
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (η.app X)
    let T := Triangle.mk (η.app X) g δ
    have hZ : P.leftOrthogonal Z := by
      intro L f hL
      have hgf : g ≫ f = 0 := by
        apply (href X L hL).1
        change η.app X ≫ (g ≫ f) = η.app X ≫ 0
        rw [← Category.assoc]
        have hzero : η.app X ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
        simp only [hzero, zero_comp, comp_zero]
      obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ T hT f hgf
      obtain ⟨b, hb⟩ := (href (X⟦(1 : ℤ)⟧) L hL).2 a
      have hab : a = (η.app X)⟦(1 : ℤ)⟧' ≫
          ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b) := by
        rw [hshift]
        simpa [Category.assoc] using hb.symm
      rw [ha, hab, ← Category.assoc]
      have hzero : δ ≫ (η.app X)⟦(1 : ℤ)⟧' = 0 :=
        comp_distTriang_mor_zero₃₁ T hT
      simpa [T] using congrArg (fun z ↦ z ≫
        ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b)) hzero
    have hR := hle _ (hout X)
    have hZ' : P.leftOrthogonal.rightOrthogonal Z :=
      P.leftOrthogonal.rightOrthogonal.ext_of_isTriangulatedClosed₃ T hT hX hR
    have hz : IsZero Z := (IsZero.iff_id_eq_zero Z).mpr (hZ' (𝟙 Z) hZ)
    apply (hfix X).mpr
    exact (Triangle.isZero₃_iff_isIso₁ T hT).mp hz
  rw [heq]
  infer_instance

private theorem complete_iso (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete Y d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison Y d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

private theorem complete_tri (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete Y d) := by
  let P : ObjectProperty (PbcCompletedDerived Y d) := PbcIsIntrinsicallyComplete Y d
  let F := pbcActualCompletion d Y
  let η := pbcActualCompletionUnit d Y
  let adj := Adjunction.ofIsRightAdjoint P.ι
  have := complete_iso Y d
  have : NatTrans.CommShift η ℤ :=
    (pbcActualCompletionShift_exists d Y).exists.choose_spec
  apply reflective_triangulated P F η
  · intro X
    exact (P.ι.leftAdjoint.obj X).property
  · intro X
    rw [show IsIso (η.app X) ↔ P.ι.essImage X from
      adj.isIso_unit_app_iff_mem_essImage]
    constructor
    · intro h
      exact ⟨⟨X, h⟩, ⟨Iso.refl _⟩⟩
    · rintro ⟨L, ⟨e⟩⟩
      exact P.prop_of_iso e L.property
  · intro X L hL
    have hb := (ObjectProperty.isLocal_adj_unit_app adj X) L ⟨⟨L, hL⟩, rfl⟩
    exact hb

end AlgebraicGeometry.Scheme
