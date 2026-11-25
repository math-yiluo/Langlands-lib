/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAdjointTower
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.AdicResidueStrictKoszulAugmentation
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit

/-! # Residue recovery from the quotient homotopy limit

Source: Stacks Project, proetale.tex, Tag 099M; algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace CategoryTheory

open RingedStrictTowerProof
open RingedStrictTowerProof.CoreWork

section StrictCone

variable {B : Type*} [Category B] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasCountableProducts B]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  [HasCountableProducts (DerivedCategory.{w} B)]
  [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ B)]

private theorem strict_projection_normalization
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} B))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    η.app Z ≫ (pNat RF η hI E ε).app (DerivedCategory.Q.obj Z) =
      DerivedCategory.Q.map (inc.app Z) ≫ pc.app Z ≫ (DP.map (ε.inv.app Z)) := by
  rw [pNat_app]
  have hq : IsIso (DerivedCategory.Q.map (q.app Z)) := by
    have := q_quasiIso Z
    infer_instance
  have hη : IsIso (η.app (F.obj Z)) := hI _ inferInstance
  have he : IsIso (evQ.map (q.app Z)) := by
    have (n : ℕᵒᵖ) : IsIso ((evQ.map (q.app Z)).app n) := by
      have := q_quasiIso Z
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).map (q.app Z)))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  dsimp only [pPre, aIso, bIso, Iso.trans_inv, Iso.trans_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.associator, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom, asIso_inv]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [← η.naturality_assoc (q.app Z)]
  dsimp only [Functor.comp_map]
  erw [NatIso.isIso_inv_app, Functor.whiskerLeft_app, IsIso.hom_inv_id_assoc]
  erw [← DerivedCategory.Q.map_comp_assoc, inc.naturality (q.app Z)]
  erw [DerivedCategory.Q.map_comp, Category.assoc, pc.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [NatIso.isIso_inv_app]
  change DerivedCategory.Q.map (inc.app Z) ≫ pc.app Z ≫
    DP.map (evQ.map (q.app Z)) ≫
      DP.map (inv (evQ.map (q.app Z)) ≫ ε.inv.app Z) =
    DerivedCategory.Q.map (inc.app Z) ≫ pc.app Z ≫ DP.map (ε.inv.app Z)
  simp only [← DP.map_comp, IsIso.hom_inv_id_assoc]

private theorem strict_limit_cone
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} B))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    ∃ c : Cone (Z.asFunctor ⋙ DerivedCategory.Q),
      ∃ e : RF.obj (DerivedCategory.Q.obj Z) ≅ c.pt,
        Pretriangulated.IsHomotopyLimit c ∧
        ∀ n : ℕ, η.app Z ≫ e.hom ≫ c.π.app (op n) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z) := by
  let F := E.obj (DerivedCategory.Q.obj Z)
  let P := Fan.mk _ (Pi.π (fun n : ℕ ↦ F.obj (op n)))
  let hP := productIsProduct (fun n : ℕ ↦ F.obj (op n))
  let p : RF.obj (DerivedCategory.Q.obj Z) ⟶ P.pt :=
    (pNat RF η hI E ε).app (DerivedCategory.Q.obj Z)
  let δ : P.pt ⟶ (RF.obj (DerivedCategory.Q.obj Z))⟦(1 : ℤ)⟧ :=
    (deltaNat RF η hI E ε).app (DerivedCategory.Q.obj Z)
  have hT := roos_Q RF η hI E ε Z
  have hshift : Pretriangulated.towerShift (F := F) hP =
      towerProductShift (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op) := by
    apply Pi.hom_ext
    intro n
    change Pretriangulated.towerShift hP ≫ P.proj n =
      towerProductShift (fun k ↦ F.map (homOfLE (Nat.le_succ k)).op) ≫ P.proj n
    rw [Pretriangulated.towerShift_proj hP n]
    exact (Pi.lift_comp_π (fun k : ℕ ↦
      Pi.π (fun j : ℕ ↦ F.obj (op j)) (k + 1) ≫
        F.map (homOfLE (Nat.le_succ k)).op) n).symm
  have hp : p ≫ Pretriangulated.towerShift (F := F) hP = p := by
    have hzero := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
    change p ≫ (𝟙 _ - towerProductShift _) = 0 at hzero
    rw [Preadditive.comp_sub] at hzero
    erw [Category.comp_id, sub_eq_zero] at hzero
    rw [hshift]
    exact hzero.symm
  let d : Cone F :=
    { pt := RF.obj (DerivedCategory.Q.obj Z)
      π := NatTrans.ofOpSequence (fun n ↦ p ≫ P.proj n) (fun n ↦ by
        dsimp
        rw [Category.id_comp, Category.assoc,
          ← Pretriangulated.towerShift_proj hP n, ← Category.assoc, hp]) }
  have hd : Pretriangulated.IsHomotopyLimit d := by
    refine ⟨P, hP, δ, ?_⟩
    have hlift : Fan.IsLimit.lift hP (fun n ↦ d.π.app (op n)) = p :=
      Fan.IsLimit.hom_ext hP _ _ (fun n ↦ by
        rw [Fan.IsLimit.fac]
        rfl)
    rw [hlift, hshift]
    exact hT
  let c : Cone (Z.asFunctor ⋙ DerivedCategory.Q) :=
    { pt := d.pt
      π := d.π ≫ (ε.app Z).hom }
  refine ⟨c, Iso.refl _, hd.of_iso (ε.app Z) c (Iso.refl _) (fun n ↦ ?_), ?_⟩
  · simp only [c, NatTrans.comp_app, Iso.refl_hom, Category.id_comp]
  · intro n
    change η.app Z ≫ (𝟙 _ ≫
      ((p ≫ P.proj n) ≫ (ε.hom.app Z).app (op n))) = _
    rw [Category.id_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (η.app Z) p]
    rw [strict_projection_normalization]
    simp only [Category.assoc]
    change DerivedCategory.Q.map (inc.app Z) ≫ pc.app Z ≫
      Limits.Pi.map (fun n : ℕ ↦ (ε.inv.app Z).app (op n)) ≫
        Pi.π (fun k : ℕ ↦ (E.obj (DerivedCategory.Q.obj Z)).obj (op k)) n ≫
          (ε.hom.app Z).app (op n) = _
    erw [Limits.Pi.map_π_assoc, Iso.inv_hom_id_app_app, Category.comp_id]
    dsimp only [pc]
    erw [piComparison_comp_π, ← DerivedCategory.Q.map_comp]
    congr 1
    exact Pi.lift_comp_π _ _

end StrictCone

/-- Transporting a descended natural transformation preserves its value on any representative. -/
private theorem transported_localization_unit
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D) [Q.EssSurj]
    (F : D ⥤ D) (full : ((Functor.whiskeringLeft C D D).obj Q).FullyFaithful)
    (γ : Q ⟶ Q ⋙ F) (P : C) (M : D) (eP : Q.obj P ≅ M) :
    eP.hom ≫ (Q.objObjPreimageIso M).inv ≫ γ.app (Q.objPreimage M) ≫
        F.map (Q.objObjPreimageIso M).hom = γ.app P ≫ F.map eP.hom := by
  let β : 𝟭 D ⟶ F := full.preimage (X := 𝟭 D) (Y := F) γ
  have hβ (N : C) : β.app (Q.obj N) = γ.app N :=
    congrArg (fun t ↦ t.app N) (full.map_preimage (X := 𝟭 D) (Y := F) γ)
  have ht (N : D) : (Q.objObjPreimageIso N).inv ≫ γ.app (Q.objPreimage N) ≫
      F.map (Q.objObjPreimageIso N).hom = β.app N := by
    rw [← hβ, ← β.naturality]
    simp only [Functor.id_map, Iso.inv_hom_id_assoc]
  rw [ht, ← hβ]
  exact β.naturality eP.hom

attribute [local irreducible] ringedKoszulTensorTowerComplex ringedKoszulLimitUnit

section KoszulUnit

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u}) (r : ℕ)
  (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
  [HasDerivedCategory.{w} (Mod O)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Mod O)]

private theorem koszul_unit_augmented
    (D : RingedKoszulLimitPresentation O r b) (P : Cx O)
    {T : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ}
    (α : ringedKoszulTensorTowerComplex O r b P ⟶ T) :
    D.unitOnComplex P ≫ D.inverseLimit.map (D.tensorFactors.app P).hom ≫
      D.inverseLimit.map (DerivedCategory.Q.map α) =
    DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P ≫
      (ordinaryLimit O).map α) ≫ D.comparison.app T := by
  dsimp only [RingedKoszulLimitPresentation.unitOnComplex]
  simp only [Category.assoc]
  rw [← D.inverseLimit.map_comp_assoc (D.tensorFactors.app P).inv
    (D.tensorFactors.app P).hom, (D.tensorFactors.app P).inv_hom_id,
    D.inverseLimit.map_id, Category.id_comp]
  erw [← D.comparison.naturality α]
  dsimp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp_assoc]
  rfl

@[irreducible] private def koszul_comparison_iso
    (D : RingedKoszulLimitPresentation O r b) (P : Cx O)
    {T : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ} {Z W : DerivedCategory (Mod O)}
    (α : ringedKoszulTensorTowerComplex O r b P ⟶ T)
    (hα : IsIso (D.inverseLimit.map (DerivedCategory.Q.map α)))
    (ed : D.inverseLimit.obj (DerivedCategory.Q.obj T) ≅ Z) (k : Z ≅ W) :
    D.completion.obj (DerivedCategory.Q.obj P) ≅ W :=
  let := hα
  D.inverseLimit.mapIso (D.tensorFactors.app P) ≪≫
    asIso (D.inverseLimit.map (DerivedCategory.Q.map α)) ≪≫ ed ≪≫ k

private theorem koszul_comparison_iso_hom
    (D : RingedKoszulLimitPresentation O r b) (P : Cx O)
    {T : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ} {Z W : DerivedCategory (Mod O)}
    (α : ringedKoszulTensorTowerComplex O r b P ⟶ T)
    (hα : IsIso (D.inverseLimit.map (DerivedCategory.Q.map α)))
    (ed : D.inverseLimit.obj (DerivedCategory.Q.obj T) ≅ Z) (k : Z ≅ W) :
    (koszul_comparison_iso O r b D P α hα ed k).hom =
      D.inverseLimit.map (D.tensorFactors.app P).hom ≫
        D.inverseLimit.map (DerivedCategory.Q.map α) ≫ ed.hom ≫ k.hom := by
  unfold koszul_comparison_iso
  rfl

/-- Projection formula for the explicitly constructed comparison isomorphism. -/
private theorem koszul_comparison_iso_projection
    (D : RingedKoszulLimitPresentation O r b) (P : Cx O)
    {T : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ}
    (α : ringedKoszulTensorTowerComplex O r b P ⟶ T)
    (hα : IsIso (D.inverseLimit.map (DerivedCategory.Q.map α)))
    {F : ℕᵒᵖ ⥤ DerivedCategory (Mod O)}
    {d : Cone (T.asFunctor ⋙ DerivedCategory.Q)}
    (ed : D.inverseLimit.obj (DerivedCategory.Q.obj T) ≅ d.pt)
    (hprojection : ∀ n : ℕ, D.comparison.app T ≫ ed.hom ≫ d.π.app (op n) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T))
    (eT : T.asFunctor ⋙ DerivedCategory.Q ≅ F)
    {c : Cone F} (k : d.pt ≅ c.pt)
    (hk : ∀ n : ℕ, k.hom ≫ c.π.app (op n) =
      d.π.app (op n) ≫ eT.hom.app (op n)) (n : ℕ) :
    (D.unitOnComplex P ≫ (koszul_comparison_iso O r b D P α hα ed k).hom) ≫
        c.π.app (op n) =
      DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P ≫
        (ordinaryLimit O).map α ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T) ≫
        eT.hom.app (op n) := by
  let j := koszul_comparison_iso O r b D P α hα ed k
  have hj : j.hom ≫ c.π.app (op n) =
      D.inverseLimit.map (D.tensorFactors.app P).hom ≫
        D.inverseLimit.map (DerivedCategory.Q.map α) ≫ ed.hom ≫
          d.π.app (op n) ≫ eT.hom.app (op n) := by
    dsimp only [j]
    rw [koszul_comparison_iso_hom]
    simp only [Category.assoc]
    rw [hk]
  change (D.unitOnComplex P ≫ j.hom) ≫ c.π.app (op n) = _
  rw [Category.assoc, hj]
  calc
    _ = (D.unitOnComplex P ≫ D.inverseLimit.map (D.tensorFactors.app P).hom ≫
        D.inverseLimit.map (DerivedCategory.Q.map α)) ≫
        ed.hom ≫ d.π.app (op n) ≫ eT.hom.app (op n) := by
      simp only [Category.assoc]
    _ = (DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P ≫
        (ordinaryLimit O).map α) ≫ D.comparison.app T) ≫
        ed.hom ≫ d.π.app (op n) ≫ eT.hom.app (op n) := by
      rw [koszul_unit_augmented O r b D P α]
    _ = DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P ≫
        (ordinaryLimit O).map α) ≫
        (D.comparison.app T ≫ ed.hom ≫ d.π.app (op n)) ≫ eT.hom.app (op n) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [hprojection, ← DerivedCategory.Q.map_comp_assoc]
      simp only [Category.assoc]

private theorem koszul_limit_inverts_prozero
    (D : RingedKoszulLimitPresentation O r b)
    {K T : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ} (α : K ⟶ T)
    (hz : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      DerivedCategory.Q.map
        ((CochainComplex.mappingCone α).asFunctor.map (homOfLE h).op) = 0) :
    IsIso (D.inverseLimit.map (DerivedCategory.Q.map α)) := by
  obtain ⟨RF, η, hRF, _, _, _, _, E, ε, _, _, _, _, _, _, _, hinv⟩ :=
    ringedStrictTowerHomotopyLimit J (siteModuleRings O)
      (fun V a b ↦ @mul_comm (O.obj.obj V) inferInstance a b)
  have hv : IsIso (RF.map (DerivedCategory.Q.map α)) := by
    apply hinv K T α
    intro n
    obtain ⟨m, h, hm⟩ := hz n
    refine ⟨m, h, ?_⟩
    apply (cancel_mono ((ε.app (CochainComplex.mappingCone α)).hom.app (op n))).1
    rw [zero_comp, NatTrans.naturality]
    change (ε.hom.app (CochainComplex.mappingCone α)).app (op m) ≫
      DerivedCategory.Q.map
        ((CochainComplex.mappingCone α).asFunctor.map (homOfLE h).op) = 0
    rw [hm, comp_zero]
  let := hRF
  let := D.isRightDerived
  let e := Functor.rightDerivedUnique D.inverseLimit RF D.comparison η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod O) (.up ℤ))
  have he : IsIso (D.inverseLimit.map (DerivedCategory.Q.map α) ≫
      e.hom.app (DerivedCategory.Q.obj T)) := by
    rw [e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app (DerivedCategory.Q.obj T))

/-- The unit evaluation as one natural isomorphism, with an explicit component API. -/
@[irreducible] private def ringed_hom_unit_iso :
    (homComplexFunctor (R := O)).obj (op (ringedSiteRingComplex O)) ≅ 𝟭 (Cx O) :=
  NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    exact homComplex_unit_evaluation_naturality J O f n)

omit [HasDerivedCategory.{w} (Mod O)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Mod O)] in
private theorem ringed_hom_unit_iso_inv_app (N : Cx O) :
    (ringed_hom_unit_iso O).inv.app N = (ringedHomUnitEvaluationIso O N).inv := by
  unfold ringed_hom_unit_iso
  rfl

private theorem koszul_unit_representative
    (D : RingedKoszulLimitPresentation O r b)
    (P : Cx O) (M : DerivedCategory (Mod O)) (eP : DerivedCategory.Q.obj P ≅ M) :
    eP.hom ≫ D.unit M = D.unitOnComplex P ≫ D.completion.map eP.hom := by
  let Q := DerivedCategory.Q (C := Mod O)
  let H := homComplexFunctor (R := O)
  obtain ⟨α, hα⟩ := exists_ringed_cech_koszul_colimit_iso O r b
  obtain ⟨e, he⟩ := exists_ringedKoszul_colimitHom_ordinaryLimit_iso O r b
  let K := (ringedExtendedCech O r b).1
  let ε := (ringedExtendedCech O r b).2
  let v : H.obj (op K) ≅ ringedKoszulTensorTowerFunctor O r b ⋙ ordinaryLimit O :=
    H.mapIso α.op ≪≫ e
  let a := ringed_hom_unit_iso O
  let z := a.inv ≫ H.map ε.op ≫ v.hom
  have hz (N : Cx O) : z.app N = ringedKoszulLimitUnit O r b N := by
    change (ringed_hom_unit_iso O).inv.app N ≫ (H.map ε.op).app N ≫
      (H.map α.hom.op).app N ≫ e.hom.app N = _
    rw [ringed_hom_unit_iso_inv_app]
    rw [← NatTrans.comp_app_assoc, ← H.map_comp, ← op_comp, hα]
    exact he N
  let d := Functor.whiskerLeft (ringedKoszulTensorTowerFunctor O r b) D.comparison
  let f := (Functor.isoWhiskerRight D.tensorFactors D.inverseLimit).symm
  let γ : Q ⟶ Q ⋙ D.completion := Functor.whiskerRight z Q ≫ d ≫ f.hom
  have hγ (N : Cx O) : γ.app N = D.unitOnComplex N := by
    change Q.map (z.app N) ≫ D.comparison.app
      (ringedKoszulTensorTowerComplex O r b N) ≫
        D.inverseLimit.map (D.tensorFactors.app N).inv = _
    rw [hz N]
    rfl
  simpa only [hγ, RingedKoszulLimitPresentation.unit] using
    transported_localization_unit Q D.completion
      (Localization.fullyFaithfulWhiskeringLeft Q
        (HomologicalComplex.quasiIso (Mod O) (.up ℤ)) (DerivedCategory (Mod O))) γ P M eP

end KoszulUnit

private theorem map_comp_iso_isIso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P N L : C} (f : P ⟶ N) (e : N ≅ L) (hf : IsIso (F.map f)) :
    IsIso (F.map (f ≫ e.hom)) := by
  let := hf
  rw [F.map_comp]
  exact (asIso (F.map f) ≪≫ F.mapIso e).isIso_hom

private theorem adjoint_projection_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P M L : C} (e : P ≅ M) (g : P ⟶ L) [IsIso (F.map g)]
    (π : L ⟶ G.obj (F.obj M)) (h : g ≫ π = e.hom ≫ adj.unit.app M) :
    IsIso ((adj.homEquiv L (F.obj M)).symm π) := by
  let p := (adj.homEquiv L (F.obj M)).symm π
  have hgp : F.map g ≫ p = F.map e.hom := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, h]
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      (adj.homEquiv_naturality_left e.hom (𝟙 (F.obj M))).symm
  have : IsIso (F.map g ≫ p) := by
    rw [hgp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map g) p

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] ringedKoszulTensorTowerComplex ringedKoszulLimitUnit
  RingedKoszulLimitPresentation.unitOnComplex RingedKoszulLimitPresentation.unit
  adicResidueScalarAdjunction adicResidueLocalReduction

attribute [local instance] HasDerivedCategory.standard

private theorem kernel_mono
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat} (q : R ⟶ S) : Mono (kernelIdeal q).inclusion := by
  constructor
  intro N f g hfg
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun h ↦ h.val.app V x) hfg

/-- Nilpotence makes every leg of the multiplication colimit zero. -/
private theorem sequential_nilpotent_colimit
    {C : Type*} [Category C] [Preadditive C] [HasColimitsOfShape ℕ C]
    (M : C) (f : M ⟶ M) (k : ℕ) (hf : (End.of f) ^ k = 0) :
    IsZero (colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f))) := by
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f)
  have hm (n j : ℕ) : F.map (homOfLE (Nat.le_add_right n j)) = ((End.of f) ^ j).asHom := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, homOfLE_refl, CategoryTheory.Functor.map_id,
        pow_zero, End.one_asHom]
      rfl
    | succ j ih =>
      have he : homOfLE (Nat.le_add_right n (j + 1)) =
          homOfLE (Nat.le_add_right n j) ≫ homOfLE (Nat.le_succ (n + j)) := rfl
      rw [he, CategoryTheory.Functor.map_comp, ih]
      dsimp only [F]
      rw [Functor.ofSequence_map_homOfLE_succ]
      change ((End.of f) ^ j).asHom ≫ f = ((End.of f) ^ (j + 1)).asHom
      rw [pow_succ', End.mul_asHom]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  have h := colimit.w F (homOfLE (Nat.le_add_right n k))
  rw [hm, hf] at h
  simpa only [End.zero_asHom, zero_comp, Category.comp_id, comp_zero] using h.symm

attribute [local irreducible] ringedSiteSectionLocalization

/-- Localization at a nilpotent section vanishes on its slice. -/
private theorem sectionLocalization_nilpotent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (k : ℕ) (hf : f ^ k = 0) :
    IsZero (ringedSiteSectionLocalization R U f) := by
  let M := SheafOfModules.unit (R.over U)
  let μ : M ⟶ M := M.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V ↦ R.obj.map V.unop.hom.op f)
      (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U f V W a))
  have hp (j : ℕ) (V : (Over U)ᵒᵖ) (m : R.obj.obj (op V.unop.left)) :
      (((End.of μ) ^ j : End M).asHom.val.app V) m =
        m * (R.obj.map V.unop.hom.op f) ^ j := by
    induction j generalizing m with
    | zero => simp only [pow_zero, End.one_asHom]; exact (mul_one m).symm
    | succ j ih =>
      rw [pow_succ', End.mul_asHom]
      change ((μ.val.app V) ((((End.of μ) ^ j : End M).asHom.val.app V) m)) = _
      rw [ih]
      change (m * (R.obj.map V.unop.hom.op f) ^ j) * R.obj.map V.unop.hom.op f = _
      rw [mul_assoc, ← pow_succ]
  have hμ : (End.of μ) ^ k = 0 := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    erw [hp]
    have hz : (R.obj.map V.unop.hom.op f) ^ k = 0 := by
      rw [← map_pow, hf, map_zero]
    rw [hz, mul_zero]
    rfl
  unfold ringedSiteSectionLocalization
  exact sequential_nilpotent_colimit M μ k hμ

open CategoryTheory.Pretriangulated.Opposite in
private theorem completeElement_nilpotent
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R)]
    [hSlices : ∀ U : C, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings R).over U))]
    (K : DerivedCategory (ConstantCompletion.Mod R)) (U : C)
    (f : R.obj.obj (op U)) (k : ℕ) (hf : f ^ k = 0) :
    IsRingedSiteCompleteElement J R K U f := by
  dsimp only [IsRingedSiteCompleteElement]
  let O := siteModuleRings R
  let L := (DerivedCategory.singleFunctor (SheafOfModules.{u} (O.over U)) 0).obj
    (ringedSiteSectionLocalization O U f)
  let N := ringedSiteDerivedRestriction O U K
  let : HasDerivedCategory.{u + 1} (ringedSiteModules.{u}
      (siteModuleRings (R.over U))) := hSlices U
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let := s
  have := hs
  have hL : IsZero L := (DerivedCategory.singleFunctor _ 0).map_isZero
    (sectionLocalization_nilpotent O U f k hf)
  exact ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N).map_isZero
    hL.op

/-- Finite scalar restrictions are complete: generators of J act nilpotently. -/
private theorem finiteRestriction_complete
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ)
    (N : D ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)) :
    IsComplete (adicResidueLocalProjection.{u, v} X J U 0)
      ((dres (adicResidueLocalProjection.{u, v} X J U n)).obj N) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let B := (finite T A J n).over U
  let q := adicResidueLocalProjection.{u, v} X J U n
  let P := DerivedCategory.Q.objPreimage N
  let L := (Q R).obj (((res q).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) L := by
    intro V f ⟨y, hy⟩
    apply (localCompleteness_models_iff (T.over U) R L V f).mpr
    obtain ⟨S, hS, _, _, _⟩ := ringedSite_complete_elements_ideal (T.over U) R L
    have hker : (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V =
        Ideal.span (Set.range (fun a : ↥(J ^ (0 + 1)) ↦
          (algebraSection (coefficientMap T A J) (a : A)).val (op V.left))) := by
      have hk := (kernelIdeal_existsUnique
        (adicResidueLocalProjection.{u, v} X J U 0)).exists.choose_spec V
      change (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V = _ at hk
      refine hk.trans ?_
      change RingHom.ker ((projection T A J 0).hom.app (op V.left)).hom = _
      exact ((flat_and_quotients T A J).2.1 0 V.left).2
    have hle : (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V ≤
        S V := by
      rw [hker]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      have ha : (a : A) ∈ J := by
        simpa only [Nat.zero_add, pow_one] using a.property
      apply (hS V _).mpr
      apply (restrictScalars_completeElement_iff (T.over U) R B q N V _).mpr
      apply completeElement_nilpotent (T.over U) B N V _ (n + 1)
      rw [← map_pow]
      apply RingHom.mem_ker.mp
      change (algebraSection (coefficientMap T A J) (a : A)).val (op V.left) ^ (n + 1) ∈
        RingHom.ker ((projection T A J n).hom.app (op V.left)).hom
      rw [((flat_and_quotients T A J).2.1 n V.left).2]
      apply Ideal.subset_span
      refine ⟨⟨(a : A) ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
      simp only [algebraSection, constantSection, map_pow]
    apply (hS V f).mp
    apply hle
    change y.val = f at hy
    exact hy ▸ y.property
  let e : L ≅ (dres q).obj N :=
    (resFactors q).app P ≪≫ (dres q).mapIso (DerivedCategory.Q.objObjPreimageIso N)
  intro V f hf
  let H := derivedInternalHom ((T.over U).over V) (R.over V)
  exact (hL V f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction R V).mapIso e))).symm

private theorem koszul_finite_unit_isIso
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (b : Fin r →
      (((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U).obj ⋙
        CategoryTheory.forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) r b)
    (hb : ∀ N L, IsComplete (adicResidueLocalProjection.{u, v} X J U 0) L →
      Function.Bijective (fun f : D.completion.obj N ⟶ L ↦ D.unit N ≫ f))
    (M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    IsIso ((adicResidueLocalReduction.{u, v} X J U n).map (D.unit M)) := by
  let adj := adicResidueScalarAdjunction.{u, v} X J U n
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hbij := hb M _ (finiteRestriction_complete.{u, v} X J U n N)
  constructor
  · intro x y hxy
    apply (adj.homEquiv _ _).injective
    apply hbij.injective
    change D.unit M ≫ (adj.homEquiv _ _) x = D.unit M ≫ (adj.homEquiv _ _) y
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hxy
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective ((adj.homEquiv _ _).toFun y)
    refine ⟨(adj.homEquiv _ _).symm x, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hx

/-- The scalar transpose of the residue leg of a quotient homotopy limit is invertible.
This computes one finite reduction of the limit; it does not specify a map into it.

Source: Stacks Project, proetale.tex, Tag 099M, lemma-naive-completion;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(auxiliary; not a blueprint node).

Proof: choose a finite generating list for J and one flat-term K-flat representative
of M. The negative Koszul tensor tower and the strict quotient tensor tower have
pro-isomorphic augmentations: Noetherian Artin--Rees kills the negative Koszul
homology pro-systems. Exact constant realization and tensoring by this fixed K-flat
representative preserve the pro-isomorphism. Apply total derived strict inverse limit.
The coefficient map from constant to completed sheaves is flat and identifies all
finite quotients. Its exact restriction commutes with the total derived limit and
reflects isomorphisms, giving the same unit-compatible Koszul comparison over the
completed ring and on the slice. The Koszul completion unit becomes an isomorphism
under residue extension: every restricted residue complex is complete by nilpotence,
so the reflector Hom bijection and the scalar adjunction give this by coyoneda.
Its normalized quotient projection is the adjoint transpose of the identity finite
reduction after that unit. Hence its transpose is the inverse of the reduced unit.
On K-flat representatives insertion of one identifies the evaluations and units;
scalar balancing identifies the quotient successor with the counit transpose in
adicResidueAdjointTower. This gives the assertion for the strict-limit cone.
The isomorphism between any two Roos cones preserves their legs, and transposition
carries it to scalar extension of this isomorphism followed by the computed finite
projection. Thus the assertion holds for c. Empty generators give the identity
projection; J=A gives zero residue objects. No boundedness or perfectness of M or
of the quotient is used, and tensor is not commuted with arbitrary products. -/
theorem adicResidue_quotient_residue_projection_isIso
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (c : Cone (adicResidueAdjointTower.{u, v} X J U M))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    IsIso (((adicResidueScalarAdjunction.{u, v} X J U 0).homEquiv c.pt
      ((adicResidueLocalReduction.{u, v} X J U 0).obj M)).symm
        (c.π.app (op 0))) := by
  classical
  let S := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed S A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  have : Mono I.inclusion := kernel_mono _
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  let b (i : Fin r) := ringedKoszulSliceSection (completed S A J)
    (algebraSection (coefficientMap S A J) (a i)) U
  have hs (V : Over U) : I.sections V =
      Ideal.span (Set.range (fun i ↦ (b i).val (op V))) := by
    have hk := (kernelIdeal_existsUnique
      (adicResidueLocalProjection.{u, v} X J U 0)).exists.choose_spec V
    change I.sections V = RingHom.ker ((projection S A J 0).hom.app (op V.left)).hom at hk
    rw [hk, ((flat_and_quotients S A J).2.1 0 V.left).2]
    let f : A →+* (completed S A J).obj.obj (op V.left) :=
      ((coefficientMap S A J).hom.app (op V.left)).hom.comp
        (((toSheafify S ((Functor.const _).obj (CommRingCat.of A))).app
          (op V.left)).hom)
    exact span_subtype_images f (J ^ (0 + 1)) a
      (by simpa only [Nat.zero_add, pow_one] using ha)
  have hg (V : Over U) : IsRingedIdealGeneratingList R I.module I.inclusion V r
      (fun i ↦ (b i).val (op V)) := by
    obtain ⟨σ, e, he⟩ := ideal_generated_global_sections (R.over V) (overIdeal I V) r
      (fun i ↦ ringedKoszulSliceSection R (b i) V) (fun W ↦ hs W.left)
    refine ⟨σ, e, ?_⟩
    intro i
    exact congrArg (fun z ↦ z.val (op (Over.mk (𝟙 V)))) (he i)
  obtain ⟨D, _, hb, _, _⟩ :=
    ringedKoszulCompletionReflector R r b I.module I.inclusion hg
  obtain ⟨P, f, hP, hf⟩ := module_flat_kFlat_resolution ((Q R).objPreimage M)
  have : QuasiIso f := hf
  let eP : (Q R).obj P ≅ M :=
    asIso ((Q R).map f) ≪≫ (Q R).objObjPreimageIso M
  obtain ⟨T, α, eT, hunit, hz⟩ :=
    adicResidue_strict_koszul_augmentation X J U r a ha M P hP.1 hP.2 eP
  have hα : IsIso (D.inverseLimit.map ((TQ R).map α)) :=
    koszul_limit_inverts_prozero R r b D α hz
  let : IsGrothendieckAbelian.{max v (u + 1)} (Mod R) :=
    SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{max v (u + 1)} (ℕᵒᵖ ⥤ Mod R) :=
    RingedStrictTowerProof.tower_grothendieck _
  let : HasCountableProducts (AdicResidueLocalDerived.{u, v} X J U) :=
    RingedStrictTowerProof.derivedCountableProducts
  obtain ⟨E, ⟨ε⟩⟩ := RingedStrictTowerProof.evaluationData (A := Mod R)
  obtain ⟨d, ed, hd, hprojection⟩ :=
    strict_limit_cone D.inverseLimit D.comparison D.comparison_isIso E ε T
  let d' : Cone (adicResidueAdjointTower.{u, v} X J U M) :=
    { pt := d.pt
      π := d.π ≫ eT.hom }
  have hd' : Pretriangulated.IsHomotopyLimit d' :=
    hd.of_iso eT d' (Iso.refl _) (fun n ↦ by
      simp only [d', NatTrans.comp_app, Iso.refl_hom, Category.id_comp])
  obtain ⟨k, hk⟩ := hd'.exists_iso hc
  let j : D.completion.obj ((Q R).obj P) ≅ c.pt :=
    koszul_comparison_iso R r b D P α hα ed k
  let g := D.unitOnComplex P ≫ j.hom
  have hnorm (n : ℕ) : g ≫ c.π.app (op n) =
      eP.hom ≫ (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M := by
    calc
      _ = (Q R).map (ringedKoszulLimitUnit R r b P ≫ (ordinaryLimit R).map α ≫
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T) ≫
          eT.hom.app (op n) :=
        koszul_comparison_iso_projection R r b D P α hα ed hprojection eT k hk n
      _ = _ := hunit n
  let F := adicResidueLocalReduction.{u, v} X J U 0
  let adj := adicResidueScalarAdjunction.{u, v} X J U 0
  have hη : IsIso (F.map (D.unitOnComplex P)) := by
    have he : D.unit ((Q R).obj P) = D.unitOnComplex P := by
      simpa only [Iso.refl_hom, Category.id_comp, D.completion.map_id, Category.comp_id]
        using koszul_unit_representative R r b D P ((Q R).obj P) (Iso.refl _)
    rw [← he]
    exact koszul_finite_unit_isIso X J U r b D hb _ 0
  have hg : IsIso (F.map g) := map_comp_iso_isIso F (D.unitOnComplex P) j hη
  exact adjoint_projection_isIso adj eP g (c.π.app (op 0)) (hnorm 0)

end AlgebraicGeometry.Scheme
