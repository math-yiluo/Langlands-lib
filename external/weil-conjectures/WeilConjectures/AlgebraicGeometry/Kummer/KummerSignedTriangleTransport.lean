/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import Mathlib.CategoryTheory.Triangulated.TriangleShift

/-! # Transport of the signed Kummer triangle. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local instance 11000] kummerAbHasExt kummerModuleHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierProRootMap cartierProKummerUnit cartierUnitsComparison
  cartierRootsIso cartierRootsComparison
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension diagonalScalarAdjunction

private theorem shifted_kummer_triangle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {M P : A} (k : ℕ) (i : P ⟶ M) (w : i ≫ (k • 𝟙 M) = 0)
    (hS : (ShortComplex.mk i (k • 𝟙 M) w).ShortExact) :
    let F := DerivedCategory.singleFunctor A 0
    Pretriangulated.Triangle.mk
      (k • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))
      (-(hS.singleδ⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app (F.obj P)))
      ((F.map (-i))⟦(2 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app (F.obj M)) ∈
      distTriang (DerivedCategory A) := by
  let F := DerivedCategory.singleFunctor A 0
  let T := (Pretriangulated.Triangle.shiftFunctor (DerivedCategory A) (1 : ℤ)).obj
    hS.singleTriangle.rotate
  have hT : T ∈ distTriang (DerivedCategory A) :=
    Pretriangulated.Triangle.shift_distinguished _
      (Pretriangulated.rot_of_distTriang _ hS.singleTriangle_distinguished) 1
  let K := Pretriangulated.Triangle.mk
    (k • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))
    (-(hS.singleδ⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app (F.obj P)))
    ((F.map (-i))⟦(2 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app (F.obj M))
  let negId : (F.obj M)⟦(1 : ℤ)⟧ ≅ (F.obj M)⟦(1 : ℤ)⟧ :=
    ⟨-𝟙 _, -𝟙 _, by simp, by simp⟩
  let z : T ≅ K := Pretriangulated.Triangle.isoMk T K negId (Iso.refl _)
    ((shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).app (F.obj P)).symm
    (by
      change ((-1 : ℤˣ) • (F.map (k • 𝟙 M))⟦(1 : ℤ)⟧') ≫ 𝟙 _ =
        (-𝟙 _) ≫ (k • 𝟙 _)
      simp only [Units.neg_smul, one_smul, Functor.map_nsmul,
        F.map_id, (shiftFunctor _ (1 : ℤ)).map_id, Category.comp_id,
        Preadditive.neg_comp, Category.id_comp])
    (by
      change ((-1 : ℤˣ) • hS.singleδ⟦(1 : ℤ)⟧') ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app (F.obj P) =
        𝟙 _ ≫ (-(hS.singleδ⟦(1 : ℤ)⟧' ≫ _))
      simp only [Units.neg_smul, one_smul, Preadditive.neg_comp, Category.id_comp])
    (by
      dsimp [T, K, negId, Pretriangulated.Triangle.shiftFunctor,
        ShortComplex.ShortExact.singleTriangle, Pretriangulated.Triangle.rotate,
        Pretriangulated.Triangle.mk]
      simp only [Units.neg_smul, one_smul, CategoryTheory.Functor.map_neg, neg_neg,
        Preadditive.comp_neg, Preadditive.neg_comp,
        shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app]
      congr 1
      change ((F.map i)⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫ 𝟙 _) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = _
      rw [(shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id]
      simp only [Category.comp_id]
      change (F.map i)⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' =
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app (F.obj P) ≫
          (shiftFunctor (DerivedCategory A) ((1 : ℤ) + 1)).map (F.map i) ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app (F.obj M)
      rw [← (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.naturality_assoc]
      simp only [Functor.comp_map, Iso.inv_hom_id_app, Category.comp_id])
  exact Pretriangulated.isomorphic_distinguished T hT K z.symm

private theorem transport_kummer_sequence
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P M : A} (k : ℕ) (K : ShortComplex A) (hK : K.ShortExact)
    (a₂ : M ≅ K.X₂) (a₃ : M ≅ K.X₃) (r : K.X₁ ≅ P)
    (hg : a₂.hom ≫ K.g = (k • 𝟙 M) ≫ a₃.hom) :
    ∃ (i : P ⟶ M) (wi : i ≫ (k • 𝟙 M) = 0)
      (hs : (ShortComplex.mk i (k • 𝟙 M) wi).ShortExact),
      r.hom ≫ i = K.f ≫ a₂.inv ∧
      hs.singleδ = (DerivedCategory.singleFunctor A 0).map a₃.hom ≫ hK.singleδ ≫
        ((DerivedCategory.singleFunctor A 0).map r.hom)⟦(1 : ℤ)⟧' := by
  let F := DerivedCategory.singleFunctor A 0
  let i : P ⟶ M := r.inv ≫ K.f ≫ a₂.inv
  have ha : a₂.inv ≫ (k • 𝟙 M) = K.g ≫ a₃.inv := by
    apply (cancel_mono a₃.hom).1
    rw [Category.assoc, ← hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have wi : i ≫ (k • 𝟙 M) = 0 := by
    dsimp only [i]
    simp only [Category.assoc]
    rw [ha, ← Category.assoc K.f, K.zero]
    simp only [zero_comp, comp_zero]
  let S := ShortComplex.mk i (k • 𝟙 M) wi
  let z : S ≅ K := ShortComplex.isoMk r.symm a₂ a₃
    (by dsimp [S, i]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]) hg
  have hs : S.ShortExact := (ShortComplex.shortExact_iff_of_iso z).2 hK
  refine ⟨i, wi, hs, ?_, ?_⟩
  · simp only [i, Iso.hom_inv_id_assoc]
  · have h := (ShortComplex.ShortExact.singleTriangle.map hs hK z.hom).comm₃
    change hs.singleδ ≫ (F.map r.inv)⟦(1 : ℤ)⟧' = F.map a₃.hom ≫ hK.singleδ at h
    apply (cancel_mono ((F.map r.inv)⟦(1 : ℤ)⟧')).1
    rw [h]
    change F.map a₃.hom ≫ hK.singleδ =
      (F.map a₃.hom ≫ hK.singleδ ≫ (F.map r.hom)⟦(1 : ℤ)⟧') ≫
        (F.map r.inv)⟦(1 : ℤ)⟧'
    have hr : F.map r.hom ≫ F.map r.inv = 𝟙 (F.obj K.X₁) := by
      rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
    have ht : (F.map r.hom)⟦(1 : ℤ)⟧' ≫ (F.map r.inv)⟦(1 : ℤ)⟧' = 𝟙 _ := by
      rw [← (shiftFunctor _ (1 : ℤ)).map_comp, hr,
        (shiftFunctor _ (1 : ℤ)).map_id]
    simp only [Category.assoc, ht]
    exact (congrArg (fun g ↦ F.map a₃.hom ≫ g) (Category.comp_id hK.singleδ)).symm

private theorem transport_signed_kummer_triangle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P M : A} (k : ℕ) (K : ShortComplex A) (hK : K.ShortExact)
    (a₂ : M ≅ K.X₂) (a₃ : M ≅ K.X₃) (r : K.X₁ ≅ P)
    (hg : a₂.hom ≫ K.g = (k • 𝟙 M) ≫ a₃.hom)
    (q : (DerivedCategory.singleFunctor A 0).obj M ⟶
      ((DerivedCategory.singleFunctor A 0).obj P)⟦(1 : ℤ)⟧)
    (hq : q = (DerivedCategory.singleFunctor A 0).map a₃.hom ≫ hK.singleδ ≫
      ((DerivedCategory.singleFunctor A 0).map r.hom)⟦(1 : ℤ)⟧') :
    let F := DerivedCategory.singleFunctor A 0
    ∃ i : P ⟶ M, Mono i ∧
      Pretriangulated.Triangle.mk (k • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))
        (-(q⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app (F.obj P)))
        ((F.map (-i))⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app (F.obj M)) ∈
        distTriang (DerivedCategory A) ∧ r.hom ≫ i = K.f ≫ a₂.inv := by
  obtain ⟨i, wi, hs, hri, hδ⟩ := transport_kummer_sequence k K hK a₂ a₃ r hg
  refine ⟨i, hs.mono_f, ?_, hri⟩
  have h := shifted_kummer_triangle k i wi hs
  rw [hδ, ← hq] at h
  exact h

/-- Transport the signed Kummer triangle through prescribed endpoint isomorphisms. -/
theorem proEtale_signed_kummer_triangle
    (W : Scheme.{u}) [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    (k : ℕ) (hk : 0 < k) (hW : IsUnit (k : Γ(W, ⊤)))
    (M P : DiagonalAb W) (a : M ≅ Scheme.proEtaleUnitsSheaf W)
    (r : Scheme.proEtaleRootsOfUnitySheaf W k ≅ P)
    (q : (DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj P)⟦(1 : ℤ)⟧)
    (hq : q = (DerivedCategory.singleFunctor (DiagonalAb W) 0).map a.hom ≫
      (cartierProKummer_exact W k hk hW).singleδ ≫
      ((DerivedCategory.singleFunctor (DiagonalAb W) 0).map r.hom)⟦(1 : ℤ)⟧') :
    let F := DerivedCategory.singleFunctor (DiagonalAb W) 0
    ∃ i : P ⟶ M, Mono i ∧
      Pretriangulated.Triangle.mk (k • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))
        (-(q⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).inv.app (F.obj P)))
        ((F.map (-i))⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).hom.app (F.obj M)) ∈
        distTriang (DerivedCategory (DiagonalAb W)) ∧
      r.hom ≫ i ≫ a.hom = Scheme.proEtaleRootsOfUnityInclusion W k := by
  obtain ⟨i, hi, ht, hri⟩ := transport_signed_kummer_triangle k
    (cartierProKummerComplex W k) (cartierProKummer_exact W k hk hW) a a r (by
      change a.hom ≫ Scheme.proEtaleUnitsPower W k = (k • 𝟙 M) ≫ a.hom
      simp only [Scheme.proEtaleUnitsPower, Preadditive.comp_nsmul,
        Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]) q hq
  refine ⟨i, hi, ht, ?_⟩
  exact (congrArg (fun f ↦ f ≫ a.hom) hri).trans (by
    change (Scheme.proEtaleRootsOfUnityInclusion W k ≫ a.inv) ≫ a.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end AlgebraicGeometry.ProEtale
