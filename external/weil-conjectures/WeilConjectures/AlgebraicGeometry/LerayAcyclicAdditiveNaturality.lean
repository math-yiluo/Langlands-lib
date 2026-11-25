/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.LeraySectionsResolutionComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural

/-! # Natural additive comparison for acyclic module direct image

Source: Stacks Project, Tags 01F4 (1), 01EY and 03FD.
(blueprint: lem-pc-k2-leray-acyclic-additive-naturality)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

-- Compare the two canonical computations on the same pushed-forward resolution.
-- Stacks, Tags 015E and 01F4 (1); naturality uses the same lift on both sides.
set_option backward.isDefEq.respectTransparency false in
private theorem acyclic_composite_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasInjectiveResolutions C] [HasInjectiveResolutions D]
    (A : C ⥤ D) (B : D ⥤ E) [A.Additive] [B.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteLimits B]
    (M : C) (hM : A.rightAcyclic M)
    (hAB : ∀ (I : C) [Injective I], B.rightAcyclic (A.obj I)) (q : ℕ) :
    ∃ e : (B.rightDerived q).obj (A.obj M) ≅ ((A ⋙ B).rightDerived q).obj M,
      ∀ φ : M ⟶ M,
        (B.rightDerived q).map (A.map φ) ≫ e.hom =
          e.hom ≫ ((A ⋙ B).rightDerived q).map φ := by
  let I := injectiveResolution M
  let ι := (HomologicalComplex.singleMapHomologicalComplex A (ComplexShape.up ℕ) 0).inv.app M ≫
    (A.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have hsingle : ∀ n, A.rightAcyclic (((CochainComplex.single₀ C).obj M).X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact hM
    · exact A.rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 M n hn)
  have hmap : QuasiIso ((A.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) :=
    A.quasiIso_map_of_rightAcyclic_nat I.ι hsingle
      (fun n ↦ Functor.rightAcyclic_of_injective _)
  have : QuasiIso ι := quasiIso_comp _ _
  let c := B.rightDerivedObjIsoOfResolution ι (fun n ↦ hAB (I.cocomplex.X n)) q
  let d := I.isoRightDerivedObj (A ⋙ B) q
  let e := c ≪≫ d.symm
  refine ⟨e, ?_⟩
  intro φ
  let ψ := InjectiveResolution.desc φ I I
  have hw : ι ≫ (A.mapHomologicalComplex _).map ψ =
      (CochainComplex.single₀ D).map (A.map φ) ≫ ι := by
    dsimp only [ι]
    rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
      Functor.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ (A.mapHomologicalComplex _).map I.ι)
        ((HomologicalComplex.singleMapHomologicalComplex A
          (ComplexShape.up ℕ) 0).inv.naturality φ).symm
  have hc := acyclicComparison_naturality B ι ι
    (fun n ↦ hAB (I.cocomplex.X n)) (fun n ↦ hAB (I.cocomplex.X n))
    (A.map φ) ((A.mapHomologicalComplex _).map ψ) hw q
  have hd := InjectiveResolution.isoRightDerivedObj_inv_naturality φ I I ψ
    (InjectiveResolution.desc_commutes_zero φ I I) (A ⋙ B) q
  change HomologicalComplex.homologyMap
    ((B.mapHomologicalComplex _).map ((A.mapHomologicalComplex _).map ψ)) q ≫ c.inv =
      c.inv ≫ (B.rightDerived q).map (A.map φ) at hc
  change d.inv ≫ ((A ⋙ B).rightDerived q).map φ =
    HomologicalComplex.homologyMap
      ((B.mapHomologicalComplex _).map ((A.mapHomologicalComplex _).map ψ)) q ≫ d.inv at hd
  have hc' : (B.rightDerived q).map (A.map φ) ≫ c.hom =
      c.hom ≫ HomologicalComplex.homologyMap
        ((B.mapHomologicalComplex _).map ((A.mapHomologicalComplex _).map ψ)) q := by
    apply (cancel_mono c.inv).1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using congrArg (fun k ↦ c.hom ≫ k) hc.symm
  change (B.rightDerived q).map (A.map φ) ≫ (c.hom ≫ d.inv) =
    (c.hom ≫ d.inv) ≫ ((A ⋙ B).rightDerived q).map φ
  rw [← Category.assoc, hc']
  simpa only [Category.assoc] using congrArg (fun k ↦ c.hom ≫ k) hd.symm

set_option backward.isDefEq.respectTransparency false in
/-- The additive Leray comparison commutes with coefficient endomorphisms.

Source: Stacks Project, cohomology.tex, Tags 01F4 (1) and 01EY;
sites-cohomology.tex, Tag 03FD.
(blueprint: lem-pc-k2-leray-acyclic-additive-naturality)

Proof: Put A = p_* and B = Γ(X, -). The vanishing hypothesis says that F is
A-right-acyclic. For an injective resolution I of F, the augmentation
F[0] ⟶ I becomes a quasi-isomorphism after applying A, by
`quasiIso_map_of_rightAcyclic_nat`; its terms are B-right-acyclic by the
module pushforward injective acyclicity theorem. The acyclic-resolution
comparison for B and `isoRightDerivedObj` for A ⋙ B therefore give an
isomorphism between the two right-derived computations. Lifting an
endomorphism of F with `InjectiveResolution.desc`, the lift commutes with the
augmentation. Naturality of `acyclicComparison_naturality` and
`isoRightDerivedObj_inv_naturality`, followed by cancellation, shows that this
isomorphism commutes with every endomorphism.

The natural sections-resolution comparison identifies the latter computation
with module cohomology on Y after forgetting scalars. The existing natural
source comparison identifies module cohomology on X and Y with H. Composing
these additive equivalences and applying their naturality equations gives the
displayed equality. The same argument includes q = 0, zero coefficients and
empty schemes; no scalar-linearity assertion is used. -/
theorem exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing
    {Y X : Scheme.{u}} (p : Y ⟶ X) [HasInjectiveResolutions Y.Modules]
    (F : Y.Modules)
    (hF : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage p q).obj F)) (q : ℕ) :
    ∃ e : ((pushforward p).obj F).H q ≃+ F.H q,
      ∀ (φ : F ⟶ F) (x : ((pushforward p).obj F).H q),
        e (H.map ((pushforward p).map φ) q x) = H.map φ q (e x) := by
  classical
  let := isGrothendieckAbelian X
  let A := pushforward p
  let B := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : B.Additive := inferInstanceAs
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive)
  let V := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}
  have : PreservesFiniteLimits A := by
    have := (pullbackPushforwardAdjunction p).rightAdjoint_preservesLimits
    infer_instance
  have : PreservesFiniteLimits B := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)))
  have hM : A.rightAcyclic F := fun n ↦ hF (n + 1) (Nat.succ_pos n)
  have hAB (I : Y.Modules) [Injective I] : B.rightAcyclic (A.obj I) :=
    (module_pushforward_injective_acyclic p I).2 ⊤
  obtain ⟨c, hc⟩ := acyclic_composite_comparison A B F hM hAB q
  obtain ⟨s, _⟩ := leray_sections_resolution_comparison p
  obtain ⟨aX, haX⟩ := exists_moduleCohomology_source_comparison X q
  obtain ⟨aY, haY⟩ := exists_moduleCohomology_source_comparison Y q
  let d := V.mapIso c ≪≫ ((s q).app F).symm
  have hd (φ : F ⟶ F) :
      V.map ((B.rightDerived q).map (A.map φ)) ≫ d.hom =
        d.hom ≫ (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.moduleCohomology Y.toRingedSpace q).map φ) := by
    have hs := (s q).inv.naturality φ
    change V.map (((A ⋙ B).rightDerived q).map φ) ≫ ((s q).app F).inv =
      ((s q).app F).inv ≫ (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology Y.toRingedSpace q).map φ) at hs
    change V.map ((B.rightDerived q).map (A.map φ)) ≫
      (V.map c.hom ≫ ((s q).app F).inv) = _
    rw [← Category.assoc, ← V.map_comp, hc, V.map_comp, Category.assoc, hs]
    rfl
  let e := (aX (A.obj F)).symm.trans
    (d.addCommGroupIsoToAddEquiv.trans (aY F))
  refine ⟨e, ?_⟩
  intro φ x
  have hx := congrArg (aX (A.obj F)).symm
    (haX (A.obj F) (A.obj F) (A.map φ) ((aX (A.obj F)).symm x))
  simp only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply] at hx
  have hd' := ConcreteCategory.congr_hom (hd φ) ((aX (A.obj F)).symm x)
  change d.hom (((B.rightDerived q).map (A.map φ)).hom
      ((aX (A.obj F)).symm x)) =
    ((RingedSpace.moduleCohomology Y.toRingedSpace q).map φ).hom
      (d.hom ((aX (A.obj F)).symm x)) at hd'
  change aY F (d.hom ((aX (A.obj F)).symm (H.map (A.map φ) q x))) = _
  change d.hom (((RingedSpace.moduleCohomology X.toRingedSpace q).map
    (A.map φ)).hom ((aX (A.obj F)).symm x)) = _ at hd'
  rw [← hx, hd']
  exact haY F F φ (d.hom ((aX (A.obj F)).symm x))

end AlgebraicGeometry.Scheme.Modules
