/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedCoefficientKernels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.Algebra.Homology.CommonQuotientReduction.FlatCommonQuotientReductionTower
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Completion for embedded integral coefficients

## References

* Stacks Project, Tags 099I, 099L, 099M and 0A07
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem smallModulesEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (IntegralModelsStacks.smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

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

private def smallRestrictionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.comap f ⋙ IntegralModelsStacks.smallModules X R ≅
      IntegralModelsStacks.smallModules X S ⋙
        ConstantCompletion.res (IntegralModelsStacks.smallMap X f) := by
  dsimp only [IntegralModelsStacks.smallModules, IntegralModelsStacks.smallMap]
  let e := CondensedRing.sectionModuleComapIso X f
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      exact (((e.hom.app M).val.app (op (AsSmall.down.obj U.unop))).hom.map_smul r m).symm
    · intro U V g
      ext m
      rfl
  · intro M N g
    ext U m
    rfl

private theorem kernelCompleteEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R B S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ B) (q : R ⟶ S)
    (hfinite : SheafOfModules.IsFiniteType.{u + 1, u + 1, u + 1}
      (ConstantCompletion.kernelIdeal q).module)
    (hflat : SheafOfModules.IsFlat.{u + 1}
      ((ConstantCompletion.res φ).obj (SheafOfModules.unit (siteModuleRings B))))
    (hquot : (ConstantCompletion.kernelIdeal q).IsQuotientIso φ) :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod B)
    letI (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (B.over U))
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B
          ((ConstantCompletion.kernelIdeal q).extension φ).module
          ((ConstantCompletion.kernelIdeal q).extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory (ConstantCompletion.IsComplete q),
      Nonempty (e.functor ⋙ ObjectProperty.ι (ConstantCompletion.IsComplete q) ≅
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete B
          ((ConstantCompletion.kernelIdeal q).extension φ).module
          ((ConstantCompletion.kernelIdeal q).extension φ).inclusion) ⋙
            ConstantCompletion.dres φ) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over U))
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (B.over U))
  exact flat_ringed_ideal_complete_equivalence φ
    (ConstantCompletion.kernelIdeal q) hfinite hflat hquot

private theorem transportCompleteEquivalence
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ≌ C') (G : D ≌ D') (r : C ⥤ D) (s : C' ⥤ D')
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty C') (Q' : ObjectProperty D')
    [P'.IsClosedUnderIsomorphisms] [Q'.IsClosedUnderIsomorphisms]
    (hP : ∀ K, P K ↔ P' (F.functor.obj K))
    (hQ : ∀ K, Q K ↔ Q' (G.functor.obj K))
    (α : r ⋙ G.functor ≅ F.functor ⋙ s)
    (e : P'.FullSubcategory ≌ Q'.FullSubcategory)
    (he : e.functor ⋙ Q'.ι ≅ P'.ι ⋙ s) :
    ∃ d : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (d.functor ⋙ Q.ι ≅ P.ι ⋙ r) := by
  let a := F.congrFullSubcategory (funext (fun K ↦ propext (hP K).symm))
  let b := G.congrFullSubcategory (funext (fun K ↦ propext (hQ K).symm))
  let d := a.trans (e.trans b.symm)
  refine ⟨d, ⟨?_⟩⟩
  change a.functor ⋙ e.functor ⋙ Q'.ι ⋙ G.inverse ≅ P.ι ⋙ r
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft a.functor he) G.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P.ι α.symm) G.inverse ≪≫
    Functor.isoWhiskerLeft (P.ι ⋙ r) G.unitIso.symm

attribute [local irreducible] IntegralModelsStacks.smallDerivedObject
  IntegralModelsStacks.smallModules IntegralModelsStacks.smallMap
  ConstantCompletion.kernelIdeal RingedSiteIdeal.extension

-- Transport compares the standard local derived instances and two complete subcategories.
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Restriction along constant continuous functions identifies the complete categories
and preserves and reflects local derived completeness for every complex.
-/
theorem integralModelsEmbeddedCompletion
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    (∃ e : ObjectProperty.FullSubcategory (IntegralModelsEmbedded.completedComplete ℓ E π X) ≌
        ObjectProperty.FullSubcategory (IntegralModelsEmbedded.constantComplete ℓ E π X),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IntegralModelsEmbedded.constantComplete ℓ E π X) ≅
        ObjectProperty.ι (IntegralModelsEmbedded.completedComplete ℓ E π X) ⋙
          IntegralModelsEmbedded.restriction ℓ E X)) ∧
    ∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      IntegralModelsEmbedded.completedComplete ℓ E π X K ↔
        IntegralModelsEmbedded.constantComplete ℓ E π X
          ((IntegralModelsEmbedded.restriction ℓ E X).obj K) := by
  let R := condensedRingObj
    (IntegralModelsEmbedded.discreteObj (PadicAlgCl.integers ℓ E.1)) X
  let B := (upperStarFromPoint X).obj (Profinite.padicIntegersRingObj ℓ E.1)
  let φ := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
  let q := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X)
  let qB := IntegralModelsStacks.smallMap X
    (completedCoefficientMap X (completedReduction ℓ E π 0)).hom
  let I := ConstantCompletion.kernelIdeal q
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X B))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard
      (ConstantCompletion.Mod ((IntegralModelsStacks.smallRing X R).over U))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard
      (ConstantCompletion.Mod ((IntegralModelsStacks.smallRing X B).over U))
  -- Construct the small-site equivalence before introducing the derived transport data.
  have hcoeff := integralModelsEmbeddedCoefficientKernels ℓ E π hπ X
  have hkernel : I.extension φ = ConstantCompletion.kernelIdeal qB := hcoeff.2.2.2
  obtain ⟨e, ⟨he⟩⟩ := kernelCompleteEquivalence
    (C := Scheme.coefficientProEtaleSiteModel.{u, u} X)
    (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (R := IntegralModelsStacks.smallRing X R)
    (B := IntegralModelsStacks.smallRing X B) φ q hcoeff.1 hcoeff.2.1 hcoeff.2.2.1
  let FR := IntegralModelsStacks.smallModules X R
  let FB := IntegralModelsStacks.smallModules X B
  have : FR.IsEquivalence := smallModulesEquivalence X R
  have : FB.IsEquivalence := smallModulesEquivalence X B
  have : FR.Additive := Functor.additive_of_preserves_binary_products FR
  have : FB.Additive := Functor.additive_of_preserves_binary_products FB
  let ER := FR.mapDerivedCategory.asEquivalence
  let EB := FB.mapDerivedCategory.asEquivalence
  let P := IntegralModelsEmbedded.completedComplete ℓ E π X
  let Q := IntegralModelsEmbedded.constantComplete ℓ E π X
  let P' : ObjectProperty (ConstantCompletion.D (IntegralModelsStacks.smallRing X B)) :=
    ConstantCompletion.IsComplete qB
  let Q' : ObjectProperty (ConstantCompletion.D (IntegralModelsStacks.smallRing X R)) :=
    ConstantCompletion.IsComplete q
  have hP (K) : P K ↔ P' (EB.functor.obj K) := by
    let e := FB.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      FB.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
    dsimp only [P, P', IntegralModelsEmbedded.completedComplete,
      IntegralModelsEmbedded.complete]
    unfold IntegralModelsStacks.smallDerivedObject
    exact (completeIso qB e).symm
  have hQ (K) : Q K ↔ Q' (ER.functor.obj K) := by
    let e := FR.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      FR.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
    dsimp only [Q, Q', IntegralModelsEmbedded.constantComplete,
      IntegralModelsEmbedded.complete]
    unfold IntegralModelsStacks.smallDerivedObject
    exact (completeIso q e).symm
  have : P'.IsClosedUnderIsomorphisms := ⟨fun e h ↦ (completeIso qB e).mp h⟩
  have : Q'.IsClosedUnderIsomorphisms := ⟨fun e h ↦ (completeIso q e).mp h⟩
  let r := IntegralModelsEmbedded.restriction ℓ E X
  let s := ConstantCompletion.dres φ
  have : PreservesFiniteLimits (ConstantCompletion.res φ) := (siteRestrictScalars_exact φ).1
  have : PreservesFiniteColimits (ConstantCompletion.res φ) := (siteRestrictScalars_exact φ).2
  let α : r ⋙ ER.functor ≅ EB.functor ⋙ s :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (smallRestrictionIso X (IntegralModelsEmbedded.scalarMap ℓ E X)) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hB (K) : P' K ↔ IsLocallyDerivedRingedIdealComplete
      (IntegralModelsStacks.smallRing X B) (I.extension φ).module
        (I.extension φ).inclusion K := by
    rw [hkernel]
    rfl
  have hiff (K) : P K ↔ Q (r.obj K) := by
    rw [hP, hQ]
    have h := (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I
      (EB.functor.obj K)).symm
    exact (hB _).trans (h.trans (completeIso q (α.app K).symm))
  constructor
  · let L : ObjectProperty (ConstantCompletion.D (IntegralModelsStacks.smallRing X B)) :=
      fun K ↦ IsLocallyDerivedRingedIdealComplete
        (IntegralModelsStacks.smallRing X B) (I.extension φ).module
          (I.extension φ).inclusion K
    have : L.IsClosedUnderIsomorphisms :=
      ⟨fun e h ↦ (hB _).mp ((completeIso qB e).mp ((hB _).mpr h))⟩
    exact transportCompleteEquivalence EB ER r s P Q L Q'
      (fun K ↦ (hP K).trans (hB _)) hQ α e he
  · exact hiff

end AlgebraicGeometry.ProEtale
