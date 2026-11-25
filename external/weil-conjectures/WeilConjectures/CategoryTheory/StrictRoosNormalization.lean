/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.StrictRoosModel

/-! Normalization of the universal derived Roos model.
Source: Stacks Project, Tag 0941 and the strict comparison refinement
(auxiliary; not a blueprint node). -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The right-derived universal property fixes the normalized comparison and its evaluations.
Source: Stacks Project, Cohomology on Sites, Tag 0941, proof, with steps 5--8 of the
strict-cone comparison (auxiliary; not a blueprint node).

Proof: Use uniqueness of right derived functors to obtain ρ. The unit equality is
Q(roosι X) κ_X ρ_X = η_X. Define e_X,n by the inverse of κ_X ρ_X followed by
Q(roosEval X n). On a resolution q:X→I the inclusion is a quasi-isomorphism by hι;
its localization is εI. The unit on I is invertible, so define dI as that unit
followed by the inverse of RF(Qq). Naturality of κρ and the unit equality give the
normalization formula. Compose with evaluation and use roosι_eval and
roosEval_natural to get the projection formula. A strict augmentation has the
explicit lift roosAugment and its ordinary-limit lift is roosAugmentLimit followed
by lim(q); roosAugment_eq and roosι_natural imply the augmentation equality.
For a comparison v with qv homotopic to q', their localized maps coincide. Compose
the desired transport equality with the isomorphism RF(Qq'), then use naturality
of η and the defining equations for dI and dJ. Cancellation proves transport.
The argument includes zero complexes and q equal to the identity. -/
theorem strictRoosNormalization
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (κ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (_hCF : CF.IsRightDerivedFunctor (roosDerivedUnit κ)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
        (ComplexShape.up ℤ)))
    (_hι : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
      [I.IsKInjective] (_hIinj : ∀ p : ℤ, Injective (I.X p)), QuasiIso (roosι I)) :
    ∃ (ρ : CF ≅ RF)
      (e : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), RF.obj
        (DerivedCategory.Q.obj X) ⟶
        DerivedCategory.Q.obj (X.asFunctor.obj (op n))),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.obj X) ≫ e X n =
        DerivedCategory.Q.map (roosEval X n)) ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective]
        (_hIinj : ∀ p : ℤ, Injective (I.X p)),
        ∃ (ι : limit I.asFunctor ⟶ roosF.obj I)
          (εI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.obj (roosF.obj I))
          (dI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.obj X)),
          (∀ p : ℤ, ι.f (p + 1) ≫ (roosχ I p).hom =
            biprod.lift 0
              ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))) ∧
          QuasiIso (roosF.map q) ∧ QuasiIso ι ∧
          εI.hom = DerivedCategory.Q.map ι ∧
          dI.hom ≫ RF.map (DerivedCategory.Q.map q) = η.app I ∧
          κ.hom.app X ≫ ρ.hom.app (DerivedCategory.Q.obj X) =
            DerivedCategory.Q.map (roosF.map q) ≫ εI.inv ≫ dI.hom ∧
          (∀ n : ℕ, ∃ υ : DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)) ≅
              DerivedCategory.Q.obj (I.asFunctor.obj (op n)),
            υ.hom = DerivedCategory.Q.map
              ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
            dI.hom ≫ e X n =
              DerivedCategory.Q.map (limit.π I.asFunctor (op n)) ≫ υ.inv) ∧
          (∀ (P : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
            (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
            (_hγ : ∀ n : ℕ, γ (n + 1) ≫
              X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n),
            ∃ (b : P ⟶ roosF.obj X) (lam : P ⟶ limit I.asFunctor),
              (∀ p : ℤ, b.f (p + 1) ≫ (roosχ X p).hom =
                biprod.lift 0 ((Pi.lift γ).f (p + 1))) ∧
              (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) = γ n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.map b ≫ κ.hom.app X ≫
                  ρ.hom.app (DerivedCategory.Q.obj X) =
                DerivedCategory.Q.map lam ≫ dI.hom) ∧
          (∀ (J' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
            (q' : X ⟶ J') [QuasiIso q'] [J'.IsKInjective]
            (_hJinj : ∀ p : ℤ, Injective (J'.X p))
            (dJ : DerivedCategory.Q.{w}.obj (limit J'.asFunctor) ≅
              RF.obj (DerivedCategory.Q.obj X))
            (_hdJ : dJ.hom ≫ RF.map (DerivedCategory.Q.map q') = η.app J')
            (v : I ⟶ J') (_hv : Nonempty (Homotopy (q ≫ v) q')),
            DerivedCategory.Q.map
                (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v)) ≫
              dJ.hom = dI.hom)) := by
  classical
  let := _hRF
  let := _hCF
  let W := HomologicalComplex.quasiIso
    (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)
  let ρ : CF ≅ RF := CF.rightDerivedUnique RF (roosDerivedUnit κ) η W
  let θ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF :=
    κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q ρ
  have hunit (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) :
      DerivedCategory.Q.map (roosι X) ≫ θ.hom.app X = η.app X := by
    have h := CF.rightDerivedNatTrans_app RF (roosDerivedUnit κ) η W
      (𝟙 _) X
    simpa [θ, ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  let e := fun X n ↦ θ.inv.app X ≫ DerivedCategory.Q.map (roosEval X n)
  refine ⟨ρ, e, ?_, ?_⟩
  · intro X n
    rw [← Category.assoc]
    change θ.hom.app X ≫ e X n = _
    simp [e]
  · intro X I q hq hI hIinj
    let := _hι I hIinj
    have hFq : IsIso (DerivedCategory.Q.map (roosF.map q)) := by
      have hn := θ.hom.naturality q
      dsimp only [Functor.comp_map] at hn
      have heq : DerivedCategory.Q.map (roosF.map q) =
          θ.hom.app X ≫ RF.map (DerivedCategory.Q.map q) ≫ θ.inv.app I := by
        rw [← Category.assoc, ← hn]
        simp
      rw [heq]
      infer_instance
    have hη : IsIso (η.app I) := by
      rw [← hunit]
      infer_instance
    let dI := asIso (η.app I) ≪≫ (asIso (RF.map (DerivedCategory.Q.map q))).symm
    have hnorm : θ.hom.app X =
        DerivedCategory.Q.map (roosF.map q) ≫
          inv (DerivedCategory.Q.map (roosι I)) ≫ dI.hom := by
      apply (cancel_mono (RF.map (DerivedCategory.Q.map q))).1
      have hn := θ.hom.naturality q
      dsimp only [Functor.comp_map] at hn
      rw [← hn]
      simp only [Category.assoc, dI, Iso.trans_hom, Iso.symm_hom, asIso_hom,
        asIso_inv, IsIso.inv_hom_id, Category.comp_id]
      rw [← hunit I]
      simp
    refine ⟨roosι I, asIso (DerivedCategory.Q.map (roosι I)), dI,
      roosι_χ I, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hFq,
      inferInstance, rfl, ?_, hnorm, ?_, ?_, ?_⟩
    · simp [dI]
    · intro n
      let qn := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)
      have hqn : QuasiIso qn :=
        (HomologicalComplex.quasiIso_iff_evaluation q).mp hq (op n)
      let υ := asIso (DerivedCategory.Q.{w}.map qn)
      refine ⟨υ, rfl, ?_⟩
      have heI : η.app I ≫ e I n =
          DerivedCategory.Q.map (limit.π I.asFunctor (op n)) := by
        rw [← hunit I]
        simp [e, ← Functor.map_comp, roosι_eval]
      have hne : RF.map (DerivedCategory.Q.map q) ≫ e I n =
          e X n ≫ DerivedCategory.Q.map qn := by
        apply (cancel_epi (θ.hom.app X)).1
        have hn := θ.hom.naturality q
        dsimp only [Functor.comp_map] at hn
        rw [← Category.assoc, ← hn]
        simp [e, Category.assoc, ← Functor.map_comp, roosEval_natural, qn]
      apply (cancel_mono υ.hom).1
      change (dI.hom ≫ e X n) ≫ DerivedCategory.Q.map qn = _
      rw [Category.assoc, ← hne, ← Category.assoc]
      simpa [dI, υ, Category.assoc] using heI
    · intro P γ hγ
      let lam := roosAugmentLimit γ hγ ≫
        lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q)
      refine ⟨roosAugment γ hγ, lam, roosAugment_χ γ hγ, ?_, ?_⟩
      · intro n
        have hπ := (lim.π (op n)).naturality
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q)
        dsimp only [lim.π_app, Functor.comp_map, evaluation_obj_map] at hπ
        calc
          lam ≫ limit.π I.asFunctor (op n) =
              (roosAugmentLimit γ hγ ≫ limit.π X.asFunctor (op n)) ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app
                  (op n) := by
            dsimp only [lam]
            simpa only [Category.assoc,
              HomologicalComplex.complexOfFunctorsToFunctorToComplex] using congrArg
              (fun f ↦ roosAugmentLimit γ hγ ≫ f) hπ
          _ = _ := by rw [roosAugmentLimit_π]
      · have hb : roosAugment γ hγ ≫ roosF.map q = lam ≫ roosι I := by
          rw [roosAugment_eq, Category.assoc, ← roosι_natural]
          rfl
        change DerivedCategory.Q.map (roosAugment γ hγ) ≫ θ.hom.app X = _
        rw [hnorm]
        simp only [← Category.assoc, ← Functor.map_comp, hb]
        simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    · intro J' q' hq' hJ' hJinj dJ hdJ v hv
      obtain ⟨hv⟩ := hv
      have hqv : DerivedCategory.Q.map q ≫ DerivedCategory.Q.map v =
          DerivedCategory.Q.map q' := by
        rw [← Functor.map_comp]
        exact DerivedCategory.Q_map_eq_of_homotopy _ hv
      apply (cancel_mono (RF.map (DerivedCategory.Q.map q'))).1
      rw [Category.assoc, hdJ, ← hqv, RF.map_comp, ← Category.assoc]
      simp only [dI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
        Category.assoc, IsIso.inv_hom_id_assoc]
      exact η.naturality v

end CategoryTheory
