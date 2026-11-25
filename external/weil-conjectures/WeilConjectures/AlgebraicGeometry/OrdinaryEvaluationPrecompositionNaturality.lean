/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

/-! # Ordinary evaluation and one part of the differential

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-precomposition-naturality).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem evaluation_precomposition {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {E H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f : E ⟶ H) :
    E ◁ SheafOfModules.homObjMap (R := R) f (𝟙 (𝟙_ _)) ≫
        (SheafOfModules.tensorHomEquiv (R := R) E _ (𝟙_ _)).symm (𝟙 _) =
      f ▷ SheafOfModules.homObj (R := R) H (𝟙_ _) ≫
        (SheafOfModules.tensorHomEquiv (R := R) H
          (SheafOfModules.homObj (R := R) H (𝟙_ _)) (𝟙_ _)).symm (𝟙 _) := by
  apply (SheafOfModules.tensorHomEquiv (R := R) E _ _).injective
  rw [SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R)]
  simp

@[reassoc] private theorem evaluation_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {E H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : E ⟶ H) :
    B ◁ SheafOfModules.homObjMap (R := R) f (𝟙 (𝟙_ _)) ≫
        SheafOfModules.moduleDualEvaluation (R) E B =
      SheafOfModules.moduleDualEvaluation (R) H B ≫
        SheafOfModules.homObjMap (R := R) f (𝟙 B) := by
  unfold SheafOfModules.moduleDualEvaluation
  rw [← SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    ← SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R)]
  apply (SheafOfModules.tensorHomEquiv (R := R) E _ B).congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left_assoc, evaluation_precomposition R]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    associator_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc]

private theorem evaluation_scaled {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {E H D D' B T :
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : E ⟶ H) (a : D ⟶ D') (z : ℤˣ)
    (b : D ⟶ SheafOfModules.homObj (R := R) H (𝟙_ _))
    (b' : D' ⟶ SheafOfModules.homObj (R := R) E (𝟙_ _)) (g : B ⟶ T)
    (ha : a ≫ b' = z • (b ≫ SheafOfModules.homObjMap (R := R) f (𝟙 (𝟙_ _)))) :
    (B ◁ a) ≫ (B ◁ b' ≫ SheafOfModules.moduleDualEvaluation R E B ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) g) =
      z • (B ◁ b ≫ SheafOfModules.moduleDualEvaluation R H B ≫
        SheafOfModules.homObjMap (R := R) f g) := by
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  rw [← whiskerLeft_comp_assoc, ha]
  simp only [Units.smul_def]
  change (tensorLeft B).map ((z : ℤ) • _) ≫ _ = _
  rw [Functor.map_zsmul, Preadditive.zsmul_comp]
  apply congrArg (fun t ↦ (z : ℤ) • t)
  change B ◁ (b ≫ SheafOfModules.homObjMap (R := R) f (𝟙 (𝟙_ _))) ≫
    SheafOfModules.moduleDualEvaluation R E B ≫
      SheafOfModules.homObjMap (R := R) (𝟙 E) g = _
  simp only [whiskerLeft_comp, Category.assoc]
  rw [evaluation_naturality_assoc R]
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]


/-- Projected evaluation respects arbitrary precomposition maps and scalars.
Source: Stacks Project, Tag 08DQ, proof of lemma-dual-perfect-complex;
Tag 03EO, tensor-Hom adjunction.
(blueprint: lem-pc-ordinary-evaluation-precomposition-naturality).
Proof: expand both nonzero component formulas. Naturality of tensor-Hom
moves the source map a through currying and through the braiding and
associator. The assumed projection identity then replaces a followed by
the dual projection with z times the original projection and precomposition
by f. Naturality of uncurrying in the Hom input moves f to the input of the
outer evaluation; currying sends this to homObjMap f. Additivity moves z
outside tensoring and currying. Output naturality composes the canonical
transports p=s+n and s+n=r+m to the canonical transport p=r+m.
All index equalities are proof-irrelevant. Neither complex need be bounded,
and zero modules satisfy the same naturality equations. -/
theorem ordinaryEvaluation_precomposition_naturality (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q q' n m r s : ℤ) (hpq : p + q = n) (hpq' : p + q' = m)
    (hr : r + q' = 0) (hs : s + q = 0) (ht : s + n = r + m)
    (f : P.X r ⟶ P.X s)
    (a : (localEvaluationDual X U P).X q ⟶ (localEvaluationDual X U P).X q')
    (z : ℤˣ)
    (ha : a ≫ localEvaluationProjection X U P (localEvaluationUnit X U) q' r 0 hr =
      z • (localEvaluationProjection X U P (localEvaluationUnit X U) q s 0 hs ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) f
          (𝟙 ((localEvaluationUnit X U).X 0)))) :
    (F.X p ◁ a) ≫ localEvaluationComponent X U P F p q' m r hpq' =
      z • (localEvaluationComponent X U P F p q n s hpq ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) f (F.XIsoOfEq ht).hom) := by
  set_option backward.isDefEq.respectTransparency.types false in
    dsimp only [localEvaluationModules] at *
    simp only [ordinaryEvaluation_component_factorization X U P F p q' m r hpq' hr,
      ordinaryEvaluation_component_factorization X U P F p q n s hpq hs]
    have hproj : a ≫
        (localEvaluationProjection X U P (localEvaluationUnit X U) q' r 0 hr ≫
          SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (𝟙_ (localEvaluationModules X U))).hom) =
        z • ((localEvaluationProjection X U P (localEvaluationUnit X U) q s 0 hs ≫
          SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X s))
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (𝟙_ (localEvaluationModules X U))).hom) ≫
          SheafOfModules.homObjMap (R := X.sheaf.over U) f (𝟙 (𝟙_ _))) := by
      have h := congrArg (fun t ↦ t ≫ SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (𝟙_ (localEvaluationModules X U))).hom) ha
      simpa only [Category.assoc (obj := localEvaluationModules X U), Units.smul_def,
        Preadditive.zsmul_comp (C := localEvaluationModules X U),
        SheafOfModules.homObjMap_comp_homObjMap (R := X.sheaf.over U),
        Category.id_comp (obj := localEvaluationModules X U),
        Category.comp_id (obj := localEvaluationModules X U)] using h
    simpa only [Category.assoc (obj := localEvaluationModules X U),
      SheafOfModules.homObjMap_comp_homObjMap (R := X.sheaf.over U),
      Category.id_comp (obj := localEvaluationModules X U),
      Category.comp_id (obj := localEvaluationModules X U),
      HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom] using
      evaluation_scaled.{u}
        (C := Over U) (J := (Opens.grothendieckTopology X).over U) (X.sheaf.over U) f a z _ _
        (F.XIsoOfEq (by omega : p = r + m)).hom hproj

end AlgebraicGeometry
