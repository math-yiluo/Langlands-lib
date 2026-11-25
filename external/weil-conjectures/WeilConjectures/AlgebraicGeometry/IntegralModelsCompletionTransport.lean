/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompleteSectionPredicate
import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Complete objects in the internal integral coefficient presentation

Source: Stacks Tags 099C, 099L and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private theorem smallModules_equivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := by
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

private theorem smallModules_additive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).Additive := ⟨by intros; ext U x; rfl⟩

private def smallRestrictionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    Mod.comap a ⋙ smallModules X R ≅
      smallModules X S ⋙ ConstantCompletion.res (smallMap X a) := by
  let P := SheafOfModules.pushforward (F := AsSmall.down)
    (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (K := Scheme.ProEt.topology X)
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)) (𝟙 _)
  exact Functor.isoWhiskerRight
    (InternalAbelianSheafModule.scalarRestrictionIso.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) a) P

private def smallDerivedEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ≌
      ConstantCompletion.D (smallRing X R) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  have := smallModules_equivalence X R
  have := smallModules_additive X R
  exact (smallModules X R).mapDerivedCategory.asEquivalence

private def smallDerivedComparison (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    (smallDerivedEquivalence X R).functor.obj K ≅ smallDerivedObject X R K := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  have := smallModules_equivalence X R
  have := smallModules_additive X R
  exact (smallModules X R).mapDerivedCategory.mapIso
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (smallModules X R).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)

section
attribute [local instance] HasDerivedCategory.standard

private theorem localComplete_iso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u + 1}) (I : RingedSiteIdeal O)
    {K L : ConstantCompletion.D O} (e : K ≅ L) :
    IsLocallyDerivedRingedIdealComplete O I.module I.inclusion K ↔
      IsLocallyDerivedRingedIdealComplete O I.module I.inclusion L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod O)
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  have h {M N : ConstantCompletion.D O} (a : M ≅ N)
      (hM : IsLocallyDerivedRingedIdealComplete O I.module I.inclusion M) :
      IsLocallyDerivedRingedIdealComplete O I.module I.inclusion N := by
    intro U f hf
    let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
      (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
    exact (((ringedDerivedRestriction O U ⋙ H).mapIso a).isZero_iff).mp (hM U f hf)
  exact ⟨h e, h e.symm⟩

end

private theorem transportCompleteEquivalence
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (c : C ≌ C') (d : D ≌ D')
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty C') (Q' : ObjectProperty D')
    [P'.IsClosedUnderIsomorphisms] [Q'.IsClosedUnderIsomorphisms]
    (R : C ⥤ D) (S : C' ⥤ D')
    (α : R ⋙ d.functor ≅ c.functor ⋙ S)
    (hP : ∀ K, P K ↔ P' (c.functor.obj K))
    (hQ : ∀ L, Q L ↔ Q' (d.functor.obj L))
    (e : P'.FullSubcategory ≌ Q'.FullSubcategory)
    (β : e.functor ⋙ Q'.ι ≅ P'.ι ⋙ S)
    (hm : ∀ K, P' K ↔ Q' (S.obj K)) :
    (∀ K, P K ↔ Q (R.obj K)) ∧
    ∃ t : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (t.functor ⋙ Q.ι ≅ P.ι ⋙ R) := by
  let ec := c.congrFullSubcategory (P := P) (Q := P')
    (funext (fun K ↦ propext (hP K).symm))
  let ed := d.congrFullSubcategory (P := Q) (Q := Q')
    (funext (fun K ↦ propext (hQ K).symm))
  let t := (ec.trans e).trans ed.symm
  let δ : t.functor ⋙ Q.ι ⋙ d.functor ≅ P.ι ⋙ R ⋙ d.functor :=
    Functor.isoWhiskerLeft (ec.functor ⋙ e.functor)
      (Functor.isoWhiskerRight ed.counitIso Q'.ι) ≪≫
    Functor.isoWhiskerLeft ec.functor β ≪≫ Functor.isoWhiskerLeft P.ι α.symm
  refine ⟨fun K ↦ ?_, t, ?_⟩
  · exact (hP K).trans ((hm _).trans
      ((Q'.prop_iff_of_iso (α.app K)).symm.trans (hQ _).symm))
  · exact ⟨(d.fullyFaithfulFunctor.whiskeringRight _).preimageIso δ⟩

/-- The complete-object equivalence in the canonical internal coefficient presentation.
This statement imposes neither constructibility nor a cohomological bound.
Source: Stacks Tags 099C, 099L and 099M
(auxiliary; not a blueprint node).

Proof: use the exact section-action and small-site equivalences, with their natural
scalar-restriction comparison, and localize them to the derived categories. The ordinary
flatness and residue calculation supplies the finite type kernel and quotient hypothesis
for the general flat ringed-ideal complete equivalence. The completed realization's local
completeness predicate is identified with completeness for the extended residue ideal.
Completeness is invariant under the chosen-representative comparison isomorphisms.
Restrict the ambient presentation equivalences to the complete full subcategories and
compose them with the flat ringed-ideal equivalence. Transport its inclusion isomorphism
back by full faithfulness. The preservation and reflection theorem for scalar restriction
gives the pointwise clause for arbitrary complexes, including zero complexes and the
empty scheme. -/
theorem completion_transport (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    let A := fun K ↦ Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K)
    let B := fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
      (smallDerivedObject X _ L)
    (∀ K, A K ↔ B ((restriction l E X).obj K)) ∧
    ∃ e : ObjectProperty.FullSubcategory A ≌ ObjectProperty.FullSubcategory B,
      Nonempty (e.functor ⋙ ObjectProperty.ι B ≅
        ObjectProperty.ι A ⋙ restriction l E X) := by
  dsimp only
  let R := condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X
  let S := condensedRingObj (integersObj l E) X
  let φ := smallMap X (scalarMap l E X)
  let q := smallMap X (residueMap l E X)
  let I := ConstantCompletion.kernelIdeal q
  let IB := I.extension φ
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X S))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod ((smallRing X R).over U))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod ((smallRing X S).over U))
  let P' : ObjectProperty (ConstantCompletion.D (smallRing X S)) :=
    IsLocallyDerivedRingedIdealComplete _ IB.module IB.inclusion
  let Q' : ObjectProperty (ConstantCompletion.D (smallRing X R)) :=
    ConstantCompletion.IsComplete q
  have : P'.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (localComplete_iso _ IB e).mp h⟩
  have : Q'.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (localComplete_iso _ I e).mp h⟩
  have hMR := smallModules_equivalence X R
  have hMS := smallModules_equivalence X S
  have hAR := smallModules_additive X R
  have hAS := smallModules_additive X S
  have hφ := (siteRestrictScalars_exact φ).1
  have hφ' := (siteRestrictScalars_exact φ).2
  let α : restriction l E X ⋙ (smallDerivedEquivalence X R).functor ≅
      (smallDerivedEquivalence X S).functor ⋙ ConstantCompletion.dres φ :=
    Functor.mapDerivedCategoryCompIso (Mod.comap (scalarMap l E X))
      (smallModules X R) ≪≫
    Functor.mapDerivedCategoryNatIso (smallRestrictionIso X (scalarMap l E X)) ≪≫
    (Functor.mapDerivedCategoryCompIso (smallModules X S) (ConstantCompletion.res φ)).symm
  obtain ⟨hI, hflat, hquot⟩ := integralModels_flat_residue l E X
  obtain ⟨e, ⟨β⟩⟩ := flat_ringed_ideal_complete_equivalence φ I hI hflat hquot
  apply transportCompleteEquivalence (smallDerivedEquivalence X S)
    (smallDerivedEquivalence X R) _
    (fun L ↦ ConstantCompletion.IsComplete q (smallDerivedObject X R L))
    P' Q' (restriction l E X)
    (ConstantCompletion.dres φ) α
    (fun K ↦ (integralModels_complete_section_predicate l E X K).trans
      (localComplete_iso _ IB (smallDerivedComparison X S K)).symm)
    (fun L ↦ (localComplete_iso _ I (smallDerivedComparison X R L)).symm) e β
  intro K
  exact (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I K).symm

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
