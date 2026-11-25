/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison

/-! # Completion of the two presentations of a coefficient model

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Tags 00YY,
03CY, 093J and 093M.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u u₁ v₁ w₁ u₂ v₂ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def mapPreimageIso
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C₁ ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage (DerivedCategory.Q.obj K))) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  (F.mapDerivedCategoryFactors.app _).symm ≪≫
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (DerivedCategory.Q.obj K)) ≪≫
      F.mapDerivedCategoryFactors.app K

private theorem completeIso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O S : Sheaf J CommRingCat.{u + 1}} (q : O ⟶ S)
    {K L : ConstantCompletion.D O} (e : K ≅ L) :
    ConstantCompletion.IsComplete q K ↔ ConstantCompletion.IsComplete q L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod O)
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  constructor <;> intro h U f hf
  · exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (O.over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e.symm)))
  · exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (O.over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e)))

private theorem kernelComparison
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S T U : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) (d : T ≅ U)
    (qR : R ⟶ T) (qS : S ⟶ U) (hsq : e.hom ≫ qS = qR ≫ d.hom) :
    (ConstantCompletion.kernelIdeal qR).extension e.hom =
      ConstantCompletion.kernelIdeal qS := by
  let K := ConstantCompletion.kernelIdeal qS
  let L := ConstantCompletion.kernelIdeal qR
  have hmemR (V : C) (a : R.obj.obj (op V)) :
      a ∈ L.sections V ↔ qR.hom.app (op V) a = 0 := by
    change a ∈ (ConstantCompletion.kernelIdeal qR).sections V ↔ _
    unfold ConstantCompletion.kernelIdeal
    rw [(ConstantCompletion.kernelIdeal_existsUnique qR).exists.choose_spec V]
    rfl
  have hmemS (V : C) (a : S.obj.obj (op V)) :
      a ∈ K.sections V ↔ qS.hom.app (op V) a = 0 := by
    change a ∈ (ConstantCompletion.kernelIdeal qS).sections V ↔ _
    unfold ConstantCompletion.kernelIdeal
    rw [(ConstantCompletion.kernelIdeal_existsUnique qS).exists.choose_spec V]
    rfl
  have hmap (V : C) (a : R.obj.obj (op V)) :
      qS.hom.app (op V) (e.hom.hom.app (op V) a) =
        d.hom.hom.app (op V) (qR.hom.app (op V) a) :=
    congrArg (fun f : R ⟶ U ↦ f.hom.app (op V) a) hsq
  have hinv (V : C) (a : S.obj.obj (op V)) :
      e.hom.hom.app (op V) (e.inv.hom.app (op V) a) = a :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : S ⟶ S ↦ f.hom.app (op V)) e.inv_hom_id) a
  apply (L.existsUnique_extension e.hom).unique
    (L.existsUnique_extension e.hom).exists.choose_spec
  intro V a
  constructor
  · intro ha
    refine ⟨⊤, J.top_mem V, ?_⟩
    intro W g hg
    let b := S.obj.map g.op a
    have hb := (hmemS W b).mp (K.restriction g a ha)
    have hc : e.inv.hom.app (op W) b ∈ L.sections W := by
      apply (hmemR W _).mpr
      have hz := hmap W (e.inv.hom.app (op W) b)
      rw [hinv, hb] at hz
      have hzero : d.inv.hom.app (op W) (d.hom.hom.app (op W)
          (qR.hom.app (op W) (e.inv.hom.app (op W) b))) =
          qR.hom.app (op W) (e.inv.hom.app (op W) b) :=
        ConcreteCategory.congr_hom
          (congrArg (fun f : T ⟶ T ↦ f.hom.app (op W)) d.hom_inv_id) _
      rw [← hzero, ← hz, map_zero]
    change b ∈ _
    rw [← hinv W b]
    exact Ideal.subset_span ⟨⟨_, hc⟩, rfl⟩
  · rintro ⟨H, hH, ha⟩
    apply K.local_mem V a H hH
    intro W g hg
    apply (show Ideal.span (Set.range
      (fun x : L.sections W ↦ e.hom.hom.app (op W) x)) ≤ K.sections W from ?_)
      (ha W g hg)
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (hmemS W _).mpr
    rw [hmap, (hmemR W x).mp x.property, map_zero]

/-- Changing the site and constant-module presentation preserves completeness of the
termwise completed realization of any coefficient complex. There is no perfectness,
boundedness, maximality or completeness assumption on the coefficient ring.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, coefficient-model
calculation; Stacks Tags 00YY, 03CY, 093J and 093M.
(auxiliary; not a blueprint node).

Proof: precomposition by AsSmall.down is an equivalence of sheaf categories. Its
constant-sheaf comparison identifies the positive quotient diagrams, including every
transition. Preservation of limits gives the canonical isomorphism from the transported
completed coefficient ring to ConstantCompletion.completed. Its nth projection is the
transported nth projection followed by the constant-sheaf comparison. In particular the
first projections commute. The associated module equivalence therefore identifies their
kernel ideals. Constant module realization is sheafification of the same constant
module presheaf in both presentations. The universal property of sheafification gives
its comparison, normalized on constant sections. Uniqueness of left adjoints to scalar
restriction identifies the two scalar-extension functors. Apply these comparisons
termwise to P and localize. The canonical localization preimage is isomorphic to the
original complex; exact transport preserves this isomorphism. On each slice, the site
and coefficient equivalences identify the kernel sections, section localizations and
derived internal Hom. They preserve and reflect zero objects. Thus the local vanishing
conditions defining the two displayed completeness predicates are equivalent. This
argument applies to unbounded P, I=0, I=A, and the empty scheme. -/
theorem sfbPerfectModel_completion_transport (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    IsSfbAdicComplete X I (sfbCompletedModel X I P) ↔
      ConstantCompletion.IsComplete
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} X) A I 0)
        ((ConstantCompletion.Q _).obj
          (AdicPerfectModel.model (coefficientProEtaleModelTopology.{u, 0} X) I P)) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let e := sfbModelCompletionIso X I
  let d := (sfbModelConstantsIso X).app (CommRingCat.of (A ⧸ I ^ (0 + 1)))
  let qR := (sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op 0))
  let qS := ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} X) A I 0
  let N := (ConstantCompletion.Q (ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, 0} X) A I)).obj
    (AdicPerfectModel.model (coefficientProEtaleModelTopology.{u, 0} X) I P)
  have hk : (ConstantCompletion.kernelIdeal qR).extension e.hom =
      ConstantCompletion.kernelIdeal qS :=
    kernelComparison e d qR qS (sfbModelCompletionIso_projection X I 0)
  let R := (sfbModelRings X).obj (adicLisseCompletedRing X I)
  let S := ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} X) A I
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  let F : proEtaleRingModules X (adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod R := proEtaleModuleToModel.{u} (X := X)
    ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  have hF_add : F.Additive := sfbModuleToModel_additive X _
  have : F.IsEquivalence := inferInstanceAs
    (proEtaleModuleModelEquivalence.{u} X
      ((adicLisseForget X).obj (adicLisseCompletedRing X I))).inverse.IsEquivalence
  let C : CochainComplex (proEtaleRingModules X (adicLisseCompletedRing X I)) ℤ :=
    ((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P)
  let D := AdicPerfectModel.model (coefficientProEtaleModelTopology.{u, 0} X) I P
  obtain ⟨c⟩ := sfbPerfectModel_complex_comparison X A I P
  have hF_lim : PreservesFiniteLimits F := by infer_instance
  have hF_colim : PreservesFiniteColimits F := by infer_instance
  let C₁ := proEtaleRingModules X (adicLisseCompletedRing X I)
  let cat₁ : Category.{u + 1} C₁ :=
    SheafOfModules.instCategory.{u + 1, u, u + 1, u + 1}
  let ab₁ : @Abelian C₁ cat₁ :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      X.ProEt inferInstance (ProEt.topology X)
      ((adicLisseForget X).obj (adicLisseCompletedRing X I))
      (WeilConjectures.integralCoefficientAbSheafify.{u, 0} X)
      (WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X)
  let der₁ := @HasDerivedCategory.standard.{u + 1, u + 2} C₁ cat₁ ab₁
  let cat₂ : Category.{u + 1} (ConstantCompletion.Mod R) :=
    SheafOfModules.instCategory.{u + 1, u + 1, u + 1, u + 1}
  let ab₂ : @Abelian (ConstantCompletion.Mod R) cat₂ :=
    SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} (siteModuleRings R)
  let der₂ := @HasDerivedCategory.standard.{u + 1, u + 2}
    (ConstantCompletion.Mod R) cat₂ ab₂
  let k₂ := @mapPreimageIso.{u + 2, u + 1, u + 2, u + 2, u + 1, u + 2}
    C₁ cat₁ ab₁ der₁ (ConstantCompletion.Mod R) cat₂ ab₂ der₂
    F hF_add hF_lim hF_colim C
  let k₃ := (ConstantCompletion.Q R).mapIso c
  have : PreservesFiniteLimits (ConstantCompletion.res e.hom) :=
    (siteRestrictScalars_exact e.hom).1
  have : PreservesFiniteColimits (ConstantCompletion.res e.hom) :=
    (siteRestrictScalars_exact e.hom).2
  let k₄ := (ConstantCompletion.res e.hom).mapDerivedCategoryFactors.app D
  let k := k₂ ≪≫ k₃ ≪≫ k₄.symm
  change ConstantCompletion.IsComplete qR _ ↔ ConstantCompletion.IsComplete qS N
  refine (completeIso qR k).trans ?_
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  let (V : coefficientProEtaleSiteModel.{u, 0} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let (V : coefficientProEtaleSiteModel.{u, 0} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod (S.over V))
  have h := siteDerivedRestrictScalars_locallyDerivedComplete_iff e.hom
    (ConstantCompletion.kernelIdeal qR) N
  rw [hk] at h
  exact h

end AlgebraicGeometry.Scheme
