/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Upper.UpperStarTensorCochainRepresentative
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
/-! K-flat representative form of scalar/pullback tensor compatibility.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-kflat-representative).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w vC vD vE vH
open CategoryTheory MonoidalCategory Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

-- Tensor normalizations compose, and transport across normalized natural transformations.
private theorem normalized_tensor_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    (Q : C ⥤ C') (R : D ⥤ D') [Q.LaxMonoidal] [R.LaxMonoidal]
    (F G : C ⥤ D)
    (dF₀ : ∀ X Y, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (dG₀ : ∀ X Y, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (LF LG : C' ⥤ D') (a : LF ⟶ LG) (t : F ⟶ G)
    (rF : Q ⋙ LF ⟶ F ⋙ R) (rG : Q ⋙ LG ⟶ G ⋙ R)
    (dF : ∀ X Y, LF.obj (X ⊗ Y) ⟶ LF.obj X ⊗ LF.obj Y)
    (dG : ∀ X Y, LG.obj (X ⊗ Y) ⟶ LG.obj X ⊗ LG.obj Y)
    (hF : ∀ P S, dF (Q.obj P) (Q.obj S) ≫ (rF.app P ⊗ₘ rF.app S) ≫
      Functor.LaxMonoidal.μ R (F.obj P) (F.obj S) =
      LF.map (Functor.LaxMonoidal.μ Q P S) ≫ rF.app (P ⊗ S) ≫
        R.map (dF₀ P S))
    (hG : ∀ P S, dG (Q.obj P) (Q.obj S) ≫ (rG.app P ⊗ₘ rG.app S) ≫
      Functor.LaxMonoidal.μ R (G.obj P) (G.obj S) =
      LG.map (Functor.LaxMonoidal.μ Q P S) ≫ rG.app (P ⊗ S) ≫
        R.map (dG₀ P S))
    (ht : ∀ P S, t.app (P ⊗ S) ≫ dG₀ P S =
      dF₀ P S ≫ (t.app P ⊗ₘ t.app S))
    (P S : C)
    (hp : a.app (Q.obj P) ≫ rG.app P = rF.app P ≫ R.map (t.app P))
    (hs : a.app (Q.obj S) ≫ rG.app S = rF.app S ≫ R.map (t.app S))
    (hps : a.app (Q.obj (P ⊗ S)) ≫ rG.app (P ⊗ S) =
      rF.app (P ⊗ S) ≫ R.map (t.app (P ⊗ S)))
    [Mono ((rG.app P ⊗ₘ rG.app S) ≫ Functor.LaxMonoidal.μ R (G.obj P) (G.obj S))] :
    a.app (Q.obj P ⊗ Q.obj S) ≫ dG (Q.obj P) (Q.obj S) =
      dF (Q.obj P) (Q.obj S) ≫ (a.app (Q.obj P) ⊗ₘ a.app (Q.obj S)) := by
  apply (cancel_mono
    ((rG.app P ⊗ₘ rG.app S) ≫ Functor.LaxMonoidal.μ R (G.obj P) (G.obj S))).1
  simp only [Category.assoc]
  rw [hG, ← a.naturality_assoc, reassoc_of% hps]
  rw [tensorHom_comp_tensorHom_assoc, hp, hs, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural, reassoc_of% hF]
  simp only [← R.map_comp]
  rw [ht]

private theorem normalized_tensor_comp
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
    (Q : C ⥤ C') (R : D ⥤ D') (S : E ⥤ E')
    [Q.LaxMonoidal] [R.LaxMonoidal] [S.LaxMonoidal]
    (F : C ⥤ D) (G : D ⥤ E)
    (dF₀ : ∀ X Y, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (dG₀ : ∀ X Y, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (LF : C' ⥤ D') (LG : D' ⥤ E')
    (rF : Q ⋙ LF ⟶ F ⋙ R) (rG : R ⋙ LG ⟶ G ⋙ S)
    (dF : ∀ X Y, LF.obj (X ⊗ Y) ⟶ LF.obj X ⊗ LF.obj Y)
    (dG : ∀ X Y, LG.obj (X ⊗ Y) ⟶ LG.obj X ⊗ LG.obj Y)
    (hF : ∀ P T, dF (Q.obj P) (Q.obj T) ≫ (rF.app P ⊗ₘ rF.app T) ≫
      Functor.LaxMonoidal.μ R (F.obj P) (F.obj T) =
      LF.map (Functor.LaxMonoidal.μ Q P T) ≫ rF.app (P ⊗ T) ≫
        R.map (dF₀ P T))
    (hG : ∀ P T, dG (R.obj P) (R.obj T) ≫ (rG.app P ⊗ₘ rG.app T) ≫
      Functor.LaxMonoidal.μ S (G.obj P) (G.obj T) =
      LG.map (Functor.LaxMonoidal.μ R P T) ≫ rG.app (P ⊗ T) ≫
        S.map (dG₀ P T))
    (hn : ∀ {X X' Y Y' : D'} (f : X ⟶ X') (g : Y ⟶ Y'),
      LG.map (f ⊗ₘ g) ≫ dG X' Y' = dG X Y ≫ (LG.map f ⊗ₘ LG.map g))
    (P T : C) :
    (LG.map (dF (Q.obj P) (Q.obj T)) ≫ dG (LF.obj (Q.obj P)) (LF.obj (Q.obj T))) ≫
        ((LG.map (rF.app P) ≫ rG.app (F.obj P)) ⊗ₘ
          (LG.map (rF.app T) ≫ rG.app (F.obj T))) ≫
        Functor.LaxMonoidal.μ S (G.obj (F.obj P)) (G.obj (F.obj T)) =
      LG.map (LF.map (Functor.LaxMonoidal.μ Q P T)) ≫
        (LG.map (rF.app (P ⊗ T)) ≫ rG.app (F.obj (P ⊗ T))) ≫
        S.map (G.map (dF₀ P T) ≫ dG₀ (F.obj P) (F.obj T)) := by
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← reassoc_of% hn]
  dsimp only [Functor.comp_obj]
  rw [hG]
  rw [← LG.map_comp_assoc, ← LG.map_comp_assoc, Category.assoc, hF]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := rG.naturality (dF₀ P T)
  dsimp only [Functor.comp_map] at hn'
  rw [reassoc_of% hn']

private def NormalizedTensor
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    (Q : C ⥤ C') (R : D ⥤ D') [Q.LaxMonoidal] [R.LaxMonoidal]
    (F : C ⥤ D) (LF : C' ⥤ D') (r : Q ⋙ LF ⟶ F ⋙ R)
    (d₀ : ∀ X Y, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (d : ∀ X Y, LF.obj (X ⊗ Y) ⟶ LF.obj X ⊗ LF.obj Y) : Prop :=
  ∀ P R₀, d (Q.obj P) (Q.obj R₀) ≫ (r.app P ⊗ₘ r.app R₀) ≫
    Functor.LaxMonoidal.μ R (F.obj P) (F.obj R₀) =
      LF.map (Functor.LaxMonoidal.μ Q P R₀) ≫ r.app (P ⊗ R₀) ≫ R.map (d₀ P R₀)

private theorem normalized_square
    {C D E H C' D' E' H' : Type*}
    [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D]
    [Category E] [MonoidalCategory E]
    [Category H] [MonoidalCategory H]
    [Category C'] [MonoidalCategory C']
    [Category D'] [MonoidalCategory D']
    [Category E'] [MonoidalCategory E']
    [Category H'] [MonoidalCategory H']
    (QC : C ⥤ C') (QD : D ⥤ D') (QE : E ⥤ E') (QH : H ⥤ H')
    [QC.LaxMonoidal] [QD.LaxMonoidal] [QE.LaxMonoidal] [QH.LaxMonoidal]
    (EY : C ⥤ D) (FB : D ⥤ H) (FA : C ⥤ E) (EX : E ⥤ H)
    (SY : C' ⥤ D') (LB : D' ⥤ H') (LA : C' ⥤ E') (SX : E' ⥤ H')
    (rY : QC ⋙ SY ⟶ EY ⋙ QD) (rB : QD ⋙ LB ⟶ FB ⋙ QH)
    (rA : QC ⋙ LA ⟶ FA ⋙ QE) (rX : QE ⋙ SX ⟶ EX ⋙ QH)
    (dY₀ : ∀ K L, EY.obj (K ⊗ L) ⟶ EY.obj K ⊗ EY.obj L)
    (dB₀ : ∀ K L, FB.obj (K ⊗ L) ⟶ FB.obj K ⊗ FB.obj L)
    (dA₀ : ∀ K L, FA.obj (K ⊗ L) ⟶ FA.obj K ⊗ FA.obj L)
    (dX₀ : ∀ K L, EX.obj (K ⊗ L) ⟶ EX.obj K ⊗ EX.obj L)
    (dY : ∀ K L, SY.obj (K ⊗ L) ⟶ SY.obj K ⊗ SY.obj L)
    (dB : ∀ K L, LB.obj (K ⊗ L) ⟶ LB.obj K ⊗ LB.obj L)
    (dA : ∀ K L, LA.obj (K ⊗ L) ⟶ LA.obj K ⊗ LA.obj L)
    (dX : ∀ K L, SX.obj (K ⊗ L) ⟶ SX.obj K ⊗ SX.obj L)
    (hY : NormalizedTensor QC QD EY SY rY dY₀ dY)
    (hB : NormalizedTensor QD QH FB LB rB dB₀ dB)
    (hA : NormalizedTensor QC QE FA LA rA dA₀ dA)
    (hX : NormalizedTensor QE QH EX SX rX dX₀ dX)
    (hnB : ∀ {K K' L L' : D'} (a : K ⟶ K') (b : L ⟶ L'),
      LB.map (a ⊗ₘ b) ≫ dB K' L' = dB K L ≫ (LB.map a ⊗ₘ LB.map b))
    (hnX : ∀ {K K' L L' : E'} (a : K ⟶ K') (b : L ⟶ L'),
      SX.map (a ⊗ₘ b) ≫ dX K' L' = dX K L ≫ (SX.map a ⊗ₘ SX.map b))
    (a : SY ⋙ LB ≅ LA ⋙ SX) (t : EY ⋙ FB ≅ FA ⋙ EX)
    (ht : ∀ P R, t.hom.app (P ⊗ R) ≫ EX.map (dA₀ P R) ≫ dX₀ (FA.obj P) (FA.obj R) =
      FB.map (dY₀ P R) ≫ dB₀ (EY.obj P) (EY.obj R) ≫ (t.hom.app P ⊗ₘ t.hom.app R))
    (P R : C)
    (hp : a.hom.app (QC.obj P) ≫ SX.map (rA.app P) ≫ rX.app (FA.obj P) =
      LB.map (rY.app P) ≫ rB.app (EY.obj P) ≫ QH.map (t.hom.app P))
    (hr : a.hom.app (QC.obj R) ≫ SX.map (rA.app R) ≫ rX.app (FA.obj R) =
      LB.map (rY.app R) ≫ rB.app (EY.obj R) ≫ QH.map (t.hom.app R))
    (hpr : a.hom.app (QC.obj (P ⊗ R)) ≫ SX.map (rA.app (P ⊗ R)) ≫
        rX.app (FA.obj (P ⊗ R)) =
      LB.map (rY.app (P ⊗ R)) ≫ rB.app (EY.obj (P ⊗ R)) ≫ QH.map (t.hom.app (P ⊗ R)))
    [IsIso (Functor.LaxMonoidal.μ QC P R)]
    [IsIso (rY.app (P ⊗ R))] [IsIso (rB.app (EY.obj (P ⊗ R)))]
    [IsIso (dA₀ P R)] [IsIso (dX₀ (FA.obj P) (FA.obj R))]
    [IsIso (dA (QC.obj P) (QC.obj R))]
    [IsIso (dX (LA.obj (QC.obj P)) (LA.obj (QC.obj R)))] :
    a.hom.app (QC.obj P ⊗ QC.obj R) ≫ SX.map (dA (QC.obj P) (QC.obj R)) ≫
      dX (LA.obj (QC.obj P)) (LA.obj (QC.obj R)) =
    LB.map (dY (QC.obj P) (QC.obj R)) ≫ dB (SY.obj (QC.obj P)) (SY.obj (QC.obj R)) ≫
      (a.hom.app (QC.obj P) ⊗ₘ a.hom.app (QC.obj R)) := by
  let rF : QC ⋙ (SY ⋙ LB) ⟶ (EY ⋙ FB) ⋙ QH :=
    Functor.whiskerRight rY LB ≫ Functor.whiskerLeft EY rB
  let rG : QC ⋙ (LA ⋙ SX) ⟶ (FA ⋙ EX) ⋙ QH :=
    Functor.whiskerRight rA SX ≫ Functor.whiskerLeft FA rX
  let dF₀ := fun K L ↦ FB.map (dY₀ K L) ≫ dB₀ (EY.obj K) (EY.obj L)
  let dG₀ := fun K L ↦ EX.map (dA₀ K L) ≫ dX₀ (FA.obj K) (FA.obj L)
  let dF := fun K L ↦ LB.map (dY K L) ≫ dB (SY.obj K) (SY.obj L)
  let dG := fun K L ↦ SX.map (dA K L) ≫ dX (LA.obj K) (LA.obj L)
  have hF := normalized_tensor_comp QC QD QH EY FB dY₀ dB₀ SY LB rY rB dY dB hY hB hnB
  have hG := normalized_tensor_comp QC QE QH FA EX dA₀ dX₀ LA SX rA rX dA dX hA hX hnX
  have hF' : NormalizedTensor QC QH (EY ⋙ FB) (SY ⋙ LB) rF dF₀ dF := by
    simpa only [NormalizedTensor, rF, dF, dF₀, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Functor.comp_map] using hF
  have hG' : NormalizedTensor QC QH (FA ⋙ EX) (LA ⋙ SX) rG dG₀ dG := by
    simpa only [NormalizedTensor, rG, dG, dG₀, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Functor.comp_map] using hG
  have hpr' : a.hom.app (QC.obj (P ⊗ R)) ≫ rG.app (P ⊗ R) =
      rF.app (P ⊗ R) ≫ QH.map (t.hom.app (P ⊗ R)) := by
    simpa only [rF, rG, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hpr
  have : IsIso (rF.app (P ⊗ R)) := by
    dsimp only [rF, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have : IsIso (a.hom.app (QC.obj (P ⊗ R)) ≫ rG.app (P ⊗ R)) := by
    rw [hpr']
    infer_instance
  have : IsIso (rG.app (P ⊗ R)) :=
    IsIso.of_isIso_comp_left (a.hom.app (QC.obj (P ⊗ R))) (rG.app (P ⊗ R))
  have : IsIso (dG (QC.obj P) (QC.obj R) ≫ (rG.app P ⊗ₘ rG.app R) ≫
      Functor.LaxMonoidal.μ QH ((FA ⋙ EX).obj P) ((FA ⋙ EX).obj R)) := by
    rw [hG' P R]
    dsimp only [dG₀, Functor.comp_map]
    infer_instance
  have : IsIso ((rG.app P ⊗ₘ rG.app R) ≫
      Functor.LaxMonoidal.μ QH ((FA ⋙ EX).obj P) ((FA ⋙ EX).obj R)) :=
    IsIso.of_isIso_comp_left (dG (QC.obj P) (QC.obj R)) _
  have hc := normalized_tensor_transport QC QH (EY ⋙ FB) (FA ⋙ EX) dF₀ dG₀
    (SY ⋙ LB) (LA ⋙ SX) a.hom t.hom rF rG dF dG hF' hG'
    (by intro K L; simpa only [dF₀, dG₀, Category.assoc] using ht K L) P R
    (by simpa only [rF, rG, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hp)
    (by simpa only [rF, rG, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hr) hpr'
  simpa only [dF, dG, Category.assoc] using hc

private theorem tensor_comparison_naturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (f ⊗ₘ g) ≫ (δ.app X').app Y' =
      (δ.app X).app Y ≫ (F.map f ⊗ₘ F.map g) := by
  have h := (Functor.uncurry.map δ).naturality (Prod.mkHom f g)
  dsimp only [Functor.uncurry_obj_map, Functor.uncurry_map_app,
    Functor.postcompose₂_obj_obj_map_app] at h
  change (F.map (f ▷ Y) ≫ F.map (X' ◁ g)) ≫ _ = _ at h
  rw [← F.map_comp] at h
  simpa only [Functor.whiskeringLeft₂_obj_obj_obj_map_app,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using h

private theorem uncurried_tensor_naturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : Functor.uncurry.obj (curriedTensor C) ⋙ F ⟶
      F.prod F ⋙ Functor.uncurry.obj (curriedTensor D))
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (f ⊗ₘ g) ≫ δ.app (X', Y') =
      δ.app (X, Y) ≫ (F.map f ⊗ₘ F.map g) := by
  have h := δ.naturality (Prod.mkHom f g)
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def] using h

-- Keep the cochain tensor comparison explicit when specializing to sheaf categories.
private abbrev complexTensorMap
    {C D : Type*} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (P R : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ R) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗ (F.mapHomologicalComplex (.up ℤ)).obj R :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app R

@[reassoc]
private theorem complexTensorMap_ι
    {C D : Type*} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (P R : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n) :
    F.map (CochainComplex.ιMapBifunctor P R (curriedTensor C) p q n h) ≫
        (complexTensorMap F P R).f n =
      Functor.OplaxMonoidal.δ F (P.X p) (R.X q) ≫
        CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj R) (curriedTensor D) p q n h := by
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P R p q n h

private theorem cochain_tensor_square
    {C D E H : Type*} [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vH} H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalPreadditive E] [MonoidalPreadditive H]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject ℤ E), X₁.HasTensor X₂]
    [∀ X₁ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
    [∀ X₂ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject ℤ H), X₁.HasTensor X₂]
    [∀ X₁ : H, PreservesColimit (Functor.empty.{0} H) ((curriedTensor H).obj X₁)]
    [∀ X₂ : H, PreservesColimit (Functor.empty.{0} H) ((curriedTensor H).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ H), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ H), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ H), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (E₀ : C ⥤ D) (F' : D ⥤ H) (F : C ⥤ E) (E' : E ⥤ H)
    [E₀.Additive] [F'.Additive] [F.Additive] [E'.Additive]
    [E₀.OplaxMonoidal] [F'.OplaxMonoidal] [F.OplaxMonoidal] [E'.OplaxMonoidal]
    [E₀.IsLeftAdjoint] [F'.IsLeftAdjoint] [F.IsLeftAdjoint] [E'.IsLeftAdjoint]
    (c : E₀ ⋙ F' ≅ F ⋙ E')
    (hm : ∀ M N, c.hom.app (M ⊗ N) ≫ E'.map (Functor.OplaxMonoidal.δ F M N) ≫
      Functor.OplaxMonoidal.δ E' (F.obj M) (F.obj N) =
      F'.map (Functor.OplaxMonoidal.δ E₀ M N) ≫
        Functor.OplaxMonoidal.δ F' (E₀.obj M) (E₀.obj N) ≫
          (c.hom.app M ⊗ₘ c.hom.app N))
    (P R : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (.up ℤ)).symm).hom.app
        (P ⊗ R) ≫
      (E'.mapHomologicalComplex (.up ℤ)).map
        (complexTensorMap F P R) ≫
      complexTensorMap E'
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj R) =
    (F'.mapHomologicalComplex (.up ℤ)).map
        (complexTensorMap E₀ P R) ≫
      complexTensorMap F'
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
        ((E₀.mapHomologicalComplex (.up ℤ)).obj R) ≫
      ((Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (.up ℤ)).symm).hom.app P ⊗ₘ
      (Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (.up ℤ)).symm).hom.app R) := by
  let ec := Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (.up ℤ)).symm
  have hec (K : CochainComplex C ℤ) (n : ℤ) :
      (ec.hom.app K).f n = c.hom.app (K.X n) := by
    simp only [ec, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app]
    exact Category.comp_id _
  change ec.hom.app (P ⊗ R) ≫ _ = _ ≫ _ ≫ (ec.hom.app P ⊗ₘ ec.hom.app R)
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map (E₀ ⋙ F')
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hec,
    Functor.comp_map]
  erw [c.hom.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← E'.map_comp_assoc, complexTensorMap_ι, E'.map_comp, Category.assoc,
    complexTensorMap_ι]
  rw [← F'.map_comp_assoc, complexTensorMap_ι, F'.map_comp, Category.assoc,
    complexTensorMap_ι_assoc, CochainComplex.ιTensorObj_tensorHom_f]
  simp only [hec]
  erw [reassoc_of% (hm (P.X p) (R.X q))]
  rfl

private theorem normalized_cochain_square
    {C D E H : Type*}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    [HasDerivedCategory.{u + 1} E] [Abelian.HasFunctorialFlatResolution E]
    [Category.{u + 1} H] [Abelian H] [IsGrothendieckAbelian.{u + 1} H]
    [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalClosed H] [BraidedCategory H]
    [HasDerivedCategory.{u + 1} H] [Abelian.HasFunctorialFlatResolution H]
    (EY : C ⥤ D) (FB : D ⥤ H) (FA : C ⥤ E) (EX : E ⥤ H)
    [EY.Additive] [FB.Additive] [FA.Additive] [EX.Additive]
    [EY.OplaxMonoidal] [FB.Monoidal] [FA.Monoidal] [EX.OplaxMonoidal]
    [EY.IsLeftAdjoint] [FB.IsLeftAdjoint] [FA.IsLeftAdjoint] [EX.IsLeftAdjoint]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ EX M N)]
    (SY : DerivedCategory C ⥤ DerivedCategory D)
    (LB : DerivedCategory D ⥤ DerivedCategory H)
    (LA : DerivedCategory C ⥤ DerivedCategory E)
    (SX : DerivedCategory E ⥤ DerivedCategory H)
    (rY : DerivedCategory.Q ⋙ SY ⟶ EY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rB : DerivedCategory.Q ⋙ LB ⟶ FB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rA : DerivedCategory.Q ⋙ LA ⟶ FA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rX : DerivedCategory.Q ⋙ SX ⟶ EX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (repY : ∀ K, SY.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((EY.mapHomologicalComplex (.up ℤ)).obj K))
    (repB : ∀ K, LB.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((FB.mapHomologicalComplex (.up ℤ)).obj K))
    (repA : ∀ K, LA.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((FA.mapHomologicalComplex (.up ℤ)).obj K))
    (repX : ∀ K, SX.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((EX.mapHomologicalComplex (.up ℤ)).obj K))
    (hrY : ∀ K, rY.app K = repY K) (hrB : ∀ K, rB.app K = repB K)
    (hrA : ∀ K, rA.app K = repA K) (hrX : ∀ K, rX.app K = repX K)
    (δY : Functor.uncurry.obj (curriedTensor (DerivedCategory C)) ⋙ SY ≅
      SY.prod SY ⋙ Functor.uncurry.obj (curriedTensor (DerivedCategory D)))
    (δB : (Functor.postcompose₂.obj LB).obj (curriedTensor (DerivedCategory D)) ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory H)).obj LB).obj LB).obj
        (curriedTensor (DerivedCategory H)))
    (δA : (Functor.postcompose₂.obj LA).obj (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory E)).obj LA).obj LA).obj
        (curriedTensor (DerivedCategory E)))
    (δX : Functor.uncurry.obj (curriedTensor (DerivedCategory E)) ⋙ SX ≅
      SX.prod SX ⋙ Functor.uncurry.obj (curriedTensor (DerivedCategory H)))
    [IsIso δA]
    (hY : AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux EY SY repY δY)
    (hB : AlgebraicGeometry.Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q)
      (Q₂ := DerivedCategory.Q) (F := FB.mapHomologicalComplex (.up ℤ)) δB repB)
    (hA : AlgebraicGeometry.Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q)
      (Q₂ := DerivedCategory.Q) (F := FA.mapHomologicalComplex (.up ℤ)) δA repA)
    (hX : AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux EX SX repX δX)
    (a : SY ⋙ LB ≅ LA ⋙ SX) (c : EY ⋙ FB ≅ FA ⋙ EX)
    (t : EY.mapHomologicalComplex (.up ℤ) ⋙ FB.mapHomologicalComplex (.up ℤ) ≅
      FA.mapHomologicalComplex (.up ℤ) ⋙ EX.mapHomologicalComplex (.up ℤ))
    (hct : t = Functor.mapHomologicalComplexCompIso c (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (FA ⋙ EX)) (.up ℤ)).symm)
    (hm : ∀ M N, c.hom.app (M ⊗ N) ≫ EX.map (Functor.OplaxMonoidal.δ FA M N) ≫
      Functor.OplaxMonoidal.δ EX (FA.obj M) (FA.obj N) =
      FB.map (Functor.OplaxMonoidal.δ EY M N) ≫
        Functor.OplaxMonoidal.δ FB (EY.obj M) (EY.obj N) ≫ (c.hom.app M ⊗ₘ c.hom.app N))
    (hrep : ∀ (K : CochainComplex C ℤ),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K →
      a.hom.app (DerivedCategory.Q.obj K) ≫ SX.map (repA K) ≫
        repX ((FA.mapHomologicalComplex (.up ℤ)).obj K) =
      LB.map (repY K) ≫ repB ((EY.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (t.hom.app K))
    (hYiso : ∀ (K : CochainComplex C ℤ),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K → IsIso (rY.app K))
    (hBiso : ∀ (K : CochainComplex D ℤ), IsIso (rB.app K))
    (P R : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hR : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat R) :
    a.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj R) ≫
      SX.map ((δA.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R)) ≫
      δX.hom.app (LA.obj (DerivedCategory.Q.obj P), LA.obj (DerivedCategory.Q.obj R)) =
    LB.map (δY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj R)) ≫
      (δB.app (SY.obj (DerivedCategory.Q.obj P))).app (SY.obj (DerivedCategory.Q.obj R)) ≫
      (a.hom.app (DerivedCategory.Q.obj P) ⊗ₘ a.hom.app (DerivedCategory.Q.obj R)) := by
  have hPR : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat (P ⊗ R) :=
    ObjectProperty.prop_tensor hP hR
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P R) := by
    rw [AlgebraicGeometry.Etale.quotient_tensorator]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have := hYiso (P ⊗ R) hPR
  have := hBiso ((EY.mapHomologicalComplex (.up ℤ)).obj (P ⊗ R))
  apply normalized_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (EY.mapHomologicalComplex (.up ℤ)) (FB.mapHomologicalComplex (.up ℤ))
    (FA.mapHomologicalComplex (.up ℤ)) (EX.mapHomologicalComplex (.up ℤ))
    SY LB LA SX rY rB rA rX
    (complexTensorMap EY) (complexTensorMap FB) (complexTensorMap FA) (complexTensorMap EX)
    (fun K L ↦ δY.hom.app (K, L)) (fun K L ↦ (δB.app K).app L)
    (fun K L ↦ (δA.app K).app L) (fun K L ↦ δX.hom.app (K, L))
    (by intro K L; simpa only [hrY, complexTensorMap] using hY K L)
    (by intro K L
        simpa only [hrB, complexTensorMap, Functor.mapCochainComplex_δ] using hB K L)
    (by intro K L
        simpa only [hrA, complexTensorMap, Functor.mapCochainComplex_δ] using hA K L)
    (by intro K L; simpa only [hrX, complexTensorMap] using hX K L)
    (tensor_comparison_naturality LB δB) (uncurried_tensor_naturality SX δX.hom)
    a t (by rw [hct]; exact cochain_tensor_square EY FB FA EX c hm) P R
  · simpa only [hrY, hrB, hrA, hrX] using hrep P hP
  · simpa only [hrY, hrB, hrA, hrX] using hrep R hR
  · simpa only [hrY, hrB, hrA, hrX] using hrep (P ⊗ R) hPR

namespace AlgebraicGeometry.Etale
attribute [local irreducible] upperStar Functor.leftDerivedFunctor
  Functor.leftDerivedFunctorCounit Functor.leftAdjoint Functor.rightAdjoint

private theorem scalar_rep_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarRepresentativeTransformation φ T).app P = scalarExtensionRepresentative φ T P :=
  rfl

private theorem geometric_rep_app
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (geometricRepresentativeTransformation A f).app P = scalarGeometricRepresentative A f P :=
  rfl

private theorem scalar_tensor_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    ExceptionalCoefficients.TensorNormalization φ T
      (ExceptionalCoefficients.tensorIso φ T) := by
  have he : ExceptionalCoefficients.tensorIso φ T =
      (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose :=
    eq_of_heq (ExceptionalCoefficients.siteTensorIso_existsUnique φ T).choose_spec.1
  exact he.symm ▸ (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose_spec.1

attribute [local irreducible] HasDerivedCategory.standard
  scalarRepresentativeTransformation geometricRepresentativeTransformation
  ProEtale.pbcFixedScalarExtension scalarExtensionRepresentative scalarGeometricRepresentative
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  scalarPullbackIso

/-- The normalized scalar/pullback tensor equation on flat-term K-flat representatives.
This is the representative calculation underlying the unrestricted derived statement.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-kflat-representative).
Proof: the ordinary scalar/pullback isomorphism is monoidal, hence its cochain
comparison respects tensor. Compose the specified scalar and geometric tensor
normalizations in both orders. The scalar/pullback normalization identifies the
composite representatives, and makes them invertible on K-flat inputs. The tensor
normalizations and the K-flat localization tensorator give an invertible comparison
on the pair. Postcompose with it, use naturality and the three representative
normalizations, apply the cochain square, and cancel. -/
theorem etaleScalarPullback_tensor_kFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P R : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R)
    (_hPflat : ∀ n : ℤ, ObjectProperty.flat (P.X n))
    (_hRflat : ∀ n : ℤ, ObjectProperty.flat (R.X n)) :
    (scalarPullbackIso φ f).hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj R) ≫
      (scalarExtension φ X).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R)) ≫
      (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (DerivedCategory.Q.obj P),
          (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
            (DerivedCategory.Q.obj R)) =
    (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.map
        ((ExceptionalCoefficients.tensorIso φ Y).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj R)) ≫
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f).app
        ((scalarExtension φ Y).obj (DerivedCategory.Q.obj P))).app
          ((scalarExtension φ Y).obj (DerivedCategory.Q.obj R))) ≫
      ((scalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (scalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj R)) := by
  let FA := upperStar (ModuleCat.{u + 1} A) f
  let FB := upperStar (ModuleCat.{u + 1} B) f
  let EY := ProEtale.etaleSheafExtendScalars φ Y
  let EX := ProEtale.etaleSheafExtendScalars φ X
  let LA := FA.leftDerivedFunctor
  let LB := FB.leftDerivedFunctor
  let SY := scalarExtension φ Y
  let SX := scalarExtension φ X
  let rY := scalarRepresentativeTransformation φ Y
  let rX := scalarRepresentativeTransformation φ X
  let rA := geometricRepresentativeTransformation A f
  let rB := geometricRepresentativeTransformation B f
  apply normalized_cochain_square EY FB FA EX SY LB LA SX rY rB rA rX
    (scalarExtensionRepresentative φ Y) (scalarGeometricRepresentative B f)
    (scalarGeometricRepresentative A f) (scalarExtensionRepresentative φ X)
    (scalar_rep_app φ Y) (geometric_rep_app B f) (geometric_rep_app A f) (scalar_rep_app φ X)
    (ExceptionalCoefficients.tensorIso φ Y)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (ExceptionalCoefficients.tensorIso φ X)
    (scalar_tensor_normalization φ Y) (upperStar_tensor_cochain_representative B f)
    (upperStar_tensor_cochain_representative A f) (scalar_tensor_normalization φ X)
    (scalarPullbackIso φ f) (scalarSheafPullbackIso φ f) (scalarSheafPullbackComplexIso φ f)
    rfl (by
      intro M N
      simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using
        (NatTrans.IsMonoidal.δ_comp_tensorHom
          (scalarSheafPullbackIso φ f).hom M N).symm)
    (by simpa only [scalarPullbackIso] using
      (scalarPullbackIso_existsUnique φ f).choose_spec.1)
    (scalarRepresentativeTransformation_isIso φ Y)
    (geometricRepresentativeTransformation_isIso B f) P R _hP _hR
end AlgebraicGeometry.Etale
