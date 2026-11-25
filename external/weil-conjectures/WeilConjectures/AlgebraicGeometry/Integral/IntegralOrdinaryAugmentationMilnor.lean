/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictAugmentation
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

import WeilConjectures.CategoryTheory.Normalized.NormalizedStrictLimitCone
import WeilConjectures.AlgebraicGeometry.Integral.IntegralRegularQuotientTower
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # The unreduced Milnor presentation of an ordinary quotient augmentation

## References

* Stacks Project, Tag 099M, Tags 0940 and 0941, normalized strict Roos comparison
-/

@[expose] public section
set_option autoImplicit false
universe u v w z a b t g
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

private theorem derived_countable_products
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{z} A]
    [Abelian.HasKInjectiveResolutions A] [HasCountableProducts A] :
    HasCountableProducts (DerivedCategory A) :=
  ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete A J⟩

private theorem milnor_of_normalized_cone
    {D : Type v} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCountableProducts D]
    {K Y : D} {G : ℕᵒᵖ ⥤ D} (u : K ⟶ Y)
    (a : (Functor.const ℕᵒᵖ).obj K ⟶ G)
    (p : (Functor.const ℕᵒᵖ).obj Y ⟶ G) (hp : IsHomotopyLimit (Cone.mk Y p))
    (hu : ∀ n : ℕ, u ≫ p.app (op n) = a.app (op n)) :
    ∃ (PK : Fan fun _ : ℕ ↦ K) (hPK : IsLimit PK)
      (PG : Fan fun n : ℕ ↦ G.obj (op n)) (hPG : IsLimit PG)
      (δK : PK.pt ⟶ K⟦(1 : ℤ)⟧) (cY : Y ⟶ PG.pt) (δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk (Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K))
        (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) δK ∈ distTriang D ∧
      Triangle.mk cY (𝟙 PG.pt - towerShift (F := G) hPG) δY ∈ distTriang D ∧
      Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K) ≫ productTowerMap (PF := PK) hPG a = u ≫ cY ∧
      δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG a ≫ δY := by
  classical
  let cK : Cone ((Functor.const ℕᵒᵖ).obj K) := Cone.mk K (𝟙 _)
  have hconst : IsHomotopyLimit cK := IsHomotopyLimit.of_isIso_π cK
  obtain ⟨PK, hPK, δK, hTK⟩ := hconst
  obtain ⟨PG, hPG, δY, hTY⟩ := hp
  let cY : Y ⟶ PG.pt := Fan.IsLimit.lift hPG (fun n ↦ p.app (op n))
  let cX : K ⟶ PK.pt := Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K)
  have hTK' : Triangle.mk cX
      (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) δK ∈
        distTriang _ := hTK
  have hδK : δK = 0 := by
    have hzero := comp_distTriang_mor_zero₃₁ _ hTK'
    have hsplit : cX ≫ PK.proj 0 = 𝟙 K := Fan.IsLimit.fac hPK _ 0
    have hh := congrArg (fun f ↦ f ≫ (PK.proj 0)⟦(1 : ℤ)⟧') hzero
    change (δK ≫ cX⟦(1 : ℤ)⟧') ≫ (PK.proj 0)⟦(1 : ℤ)⟧' = _ at hh
    have hshift : cX⟦(1 : ℤ)⟧' ≫ (PK.proj 0)⟦(1 : ℤ)⟧' = 𝟙 (K⟦(1 : ℤ)⟧) := by
      rw [← CategoryTheory.Functor.map_comp, hsplit]
      exact (shiftFunctor _ (1 : ℤ)).map_id K
    simp only [Category.assoc, hshift, zero_comp] at hh
    exact (Category.comp_id δK).symm.trans hh
  have hepi : Epi (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) :=
    Triangle.epi₂ _ hTK' hδK
  have hzeroY : (𝟙 PG.pt - towerShift (F := G) hPG) ≫ δY = 0 :=
    comp_distTriang_mor_zero₂₃ _ hTY
  have hmδ : productTowerMap (PF := PK) hPG a ≫ δY = 0 := by
    apply (cancel_epi (𝟙 PK.pt -
      towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK)).1
    rw [comp_zero, ← Category.assoc, ← productTowerMap_comp_sub_towerShift hPK hPG a,
      Category.assoc, hzeroY, comp_zero]
  refine ⟨PK, hPK, PG, hPG, δK, cY, δY, hTK', hTY, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext hPG
    intro n
    rw [Category.assoc, productTowerMap_proj, ← Category.assoc, Fan.IsLimit.fac,
      Category.id_comp, Category.assoc, Fan.IsLimit.fac]
    exact (hu n).symm
  · change δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG a ≫ δY
    have hzero : δK ≫ u⟦(1 : ℤ)⟧' = 0 :=
      (congrArg (fun f : PK.pt ⟶ K⟦(1 : ℤ)⟧ ↦ f ≫ u⟦(1 : ℤ)⟧') hδK).trans
        zero_comp
    exact hzero.trans hmδ.symm

private theorem ordinary_milnor_of_tail
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    {B : Type b} [Category.{t} B] [Abelian B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{z} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory A)]
    [HasCountableProducts (DerivedCategory B)]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (ηZ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex A ℤ) (G : ℕᵒᵖ ⥤ DerivedCategory B)
    (a : (Functor.const ℕᵒᵖ).obj
      (e.mapDerivedCategory.functor.obj (DerivedCategory.Q.obj P)) ⟶ G)
    (α : ((O.E.mapHomologicalComplex (.up ℤ)).obj P).asFunctor ⋙
      DerivedCategory.Q ⋙ e.mapDerivedCategory.functor ≅ addOpFunctor 1 ⋙ G)
    (hα : ∀ n : ℕ, e.mapDerivedCategory.functor.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P)) ≫
      α.hom.app (op n) = a.app (op (n + 1))) :
    let K := e.mapDerivedCategory.functor.obj (DerivedCategory.Q.obj P)
    let Y := e.mapDerivedCategory.functor.obj
      (RZ.obj (DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P)))
    let u := e.mapDerivedCategory.functor.map
      (integralStrictOrdinaryAugmentation ℓ RZ ηZ O P)
    ∃ (PK : Fan fun _ : ℕ ↦ K) (hPK : IsLimit PK)
      (PG : Fan fun n : ℕ ↦ G.obj (op n)) (hPG : IsLimit PG)
      (δK : PK.pt ⟶ K⟦(1 : ℤ)⟧) (cY : Y ⟶ PG.pt) (δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk (Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K))
        (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) δK ∈
          distTriang (DerivedCategory B) ∧
      Triangle.mk cY (𝟙 PG.pt - towerShift (F := G) hPG) δY ∈
        distTriang (DerivedCategory B) ∧
      Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K) ≫ productTowerMap (PF := PK) hPG a = u ≫ cY ∧
      δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG a ≫ δY := by
  classical
  let ed := e.mapDerivedCategory.functor
  let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
  let K := ed.obj (DerivedCategory.Q.obj P)
  let Y := ed.obj (RZ.obj (DerivedCategory.Q.obj X))
  let u : K ⟶ Y := ed.map (integralStrictOrdinaryAugmentation ℓ RZ ηZ O P)
  obtain ⟨p, hp, hn⟩ := normalizedStrictLimitCone RZ ηZ hRZ e X G α
  let b : P ⟶ ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X :=
    ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).unit.app P ≫
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (diagonalReductionTowerAugmentation ℓ O) (.up ℤ)).app P)
  have hb (n : ℕ) :
      b ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X =
        (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (constLimAdj.unit.app (P.X i) ≫
      lim.map ((diagonalReductionTowerAugmentation ℓ O).app (P.X i))) ≫
        limit.π (O.E.obj (P.X i)) (op n) = (O.π n).app (P.X i)
    rw [Category.assoc, lim_map, limMap_π, ← Category.assoc]
    simp [constLimAdj, diagonalReductionTowerAugmentation]
  have hu (n : ℕ) : u ≫ p.app (op n) = a.app (op n) := by
    have hs (m : ℕ) : u ≫ p.app (op (m + 1)) = a.app (op (m + 1)) := by
      change ed.map (DerivedCategory.Q.map b ≫ ηZ.app X) ≫ _ = _
      rw [hn P b m, hb]
      exact hα m
    cases n with
    | zero =>
      have hp₀ : p.app (op 0) = p.app (op 1) ≫
          G.map (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op :=
        (Category.id_comp _).symm.trans
          (p.naturality (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op)
      have ha₀ : a.app (op 0) = a.app (op 1) ≫
          G.map (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op :=
        (Category.id_comp _).symm.trans
          (a.naturality (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op)
      rw [hp₀, ← Category.assoc, hs 0, ← ha₀]
    | succ n => exact hs n
  exact milnor_of_normalized_cone u a p hp hu

/-- The ordinary quotient augmentation, before any coefficient reduction, is a map
of Milnor triangles from the constant tower to the principal derived quotient tower.
Both product squares, including the shifted boundary square, are specified. -/
theorem integral_ordinary_augmentation_milnor (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (O : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)))
    (e : DiagonalAb W ≌
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    let K := e.mapDerivedCategory.functor.obj (DerivedCategory.Q.obj P)
    let Y := e.mapDerivedCategory.functor.obj
      (RZ.obj (DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P)))
    let u := e.mapDerivedCategory.functor.map
      (integralStrictOrdinaryAugmentation ℓ RZ ηZ O P)
    let G := DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology W)
      (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K
    ∃ (PK : Fan fun _ : ℕ ↦ K) (hPK : IsLimit PK)
      (PG : Fan fun n : ℕ ↦ G.obj (op n)) (hPG : IsLimit PG)
      (δK : PK.pt ⟶ K⟦(1 : ℤ)⟧) (cY : Y ⟶ PG.pt) (δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk (Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K))
        (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) δK ∈ distTriang (DerivedCategory
          (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) ∧
      Triangle.mk cY (𝟙 PG.pt - towerShift (F := G) hPG) δY ∈ distTriang (DerivedCategory
          (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) ∧
      Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K) ≫ productTowerMap (PF := PK) hPG
        (DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology W)
          (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K).π = u ≫ cY ∧
      δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG
        (DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology W)
          (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K).π ≫ δY := by
  classical
  let A := DiagonalAb W
  let B := Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  let : HasCountableProducts (DerivedCategory A) := derived_countable_products (A := A)
  let : HasCountableProducts (DerivedCategory B) := derived_countable_products (A := B)
  let K := e.mapDerivedCategory.functor.obj (DerivedCategory.Q.obj P)
  let G := DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology W)
    (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K
  let a := (DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology W)
    (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K).π
  obtain ⟨α, hα⟩ := integral_regular_quotient_tower ℓ W O e P hP
  exact ordinary_milnor_of_tail ℓ O RZ ηZ hRZ e P G a α hα

end AlgebraicGeometry.ProEtale
