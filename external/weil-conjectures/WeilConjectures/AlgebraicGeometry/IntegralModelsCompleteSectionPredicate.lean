/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionIdeal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local completeness under the completed integral realization

Source: Stacks Tags 00YV, 099C and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
attribute [local instance] HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits Opposite

-- The `max u (t + 1)` torsion-completion sheafification instances leave the coefficient universe
-- of `X.proEtaleModelTopology` undetermined (stuck universe constraint).
attribute [-instance] AlgebraicGeometry.Scheme.torsionCompletionSheafify
  AlgebraicGeometry.Scheme.torsionCompletionSliceSheafify
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint integralSectionRingIso
  WeilConjectures.purCoefficientIso Scheme.pbcCompletedComparison
  IntegralConstantModel.pointComparison smallDerivedObject

-- Compare the four exact scalar transports without unfolding their coefficient limits.
private def modulesSectionIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    IntegralConstantModel.modulesFunctor l E X ≅
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (integersObj l E) X)).functor ⋙
      Scheme.pbcRestrict (completedSectionIso l E X).hom := by
  let a := coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X
  let c := Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)
  let d := WeilConjectures.purCoefficientIso l E X
  let e := integralSectionRingIso l E X
  have he : (Scheme.adicLisseForget X).mapIso d =
      Scheme.integralDetailedCoefficientComparison X l E :=
    by
      dsimp only [d]
      unfold WeilConjectures.purCoefficientIso
      exact (WeilConjectures.purCoefficientIso_existsUnique l E X).exists.choose_spec
  dsimp only [IntegralConstantModel.modulesFunctor, integralSectionFunctor]
  rw [← he]
  let α := CondensedRing.sectionModuleComapIso X a
  let β := Scheme.pbcRestrictComp d.hom e.inv (d.hom ≫ e.inv) rfl
  let γ := Scheme.pbcRestrictComp c.hom (d.hom ≫ e.inv)
    (c.hom ≫ d.hom ≫ e.inv) rfl
  let δ := Scheme.pbcRestrictComp (c.hom ≫ d.hom ≫ e.inv)
    (pointSectionIso l E X).hom (completedSectionIso l E X).hom rfl
  exact Functor.isoWhiskerLeft (Mod.comap a)
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight β _ ≪≫ γ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ δ

private def smallModulesSectionIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    IntegralConstantModel.modulesFunctor l E X ⋙
        Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj
          (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) ≅
      smallModules X (condensedRingObj (integersObj l E) X) ⋙
        ConstantCompletion.res ((Scheme.sfbModelRings X).map (completedSectionIso l E X).hom) := by
  exact Functor.isoWhiskerRight (modulesSectionIso l E X) _

private def toModelEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk
    (Scheme.proEtaleModuleToModel R) (Scheme.proEtaleModuleFromModel R)
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))

-- Fix the morphism universes of the exact functors across the two site presentations.
private def derivedSectionIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    let R := Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E)
    let F := Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj R)
    letI : F.Additive := ⟨by intros; ext U x; rfl⟩
    (ConstantCompletion.Q ((Scheme.sfbModelRings X).obj R)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj
        (DerivedCategory.Q.objPreimage ((IntegralConstantModel.derived l E X).functor.obj K))) ≅
    (ConstantCompletion.dres ((Scheme.sfbModelRings X).map (completedSectionIso l E X).hom)).obj
      (smallDerivedObject X _ K) := by
  dsimp only
  let R := Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E)
  letI := HasDerivedCategory.standard
    (ConstantCompletion.Mod ((Scheme.sfbModelRings X).obj R))
  letI := HasDerivedCategory.standard
    (ConstantCompletion.Mod (smallRing X (condensedRingObj (integersObj l E) X)))
  let F := Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj R)
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  have : F.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integersObj l E) X)
  let hC : HasDerivedCategory.{u + 1} C := HasDerivedCategory.ofIsGrothendieckAbelian _
  let Q := @DerivedCategory.Q C _ _ hC
  let G := IntegralConstantModel.modulesFunctor l E X
  let S := smallModules X (condensedRingObj (integersObj l E) X)
  have : S.Additive := ⟨by intros; ext U x; rfl⟩
  let c := (Scheme.sfbModelRings X).map (completedSectionIso l E X).hom
  let T := ConstantCompletion.res c
  have := (siteRestrictScalars_exact c).1
  have := (siteRestrictScalars_exact c).2
  let P := Q.objPreimage K
  let L := (IntegralConstantModel.derived l E X).functor.obj K
  let D := Scheme.proEtaleRingModules X R
  let hD : HasDerivedCategory.{u + 2} D := Scheme.reductionModulesHasDerivedCategory X R
  have : G.Additive := IntegralConstantModel.modulesFunctor_additive l E X
  have : G.IsEquivalence := IntegralConstantModel.modulesFunctor_isEquivalence l E X
  let qG := @Functor.mapDerivedCategoryFactors _ _ _ hC _ _ _
    hD G inferInstance inferInstance inferInstance
  let qF := @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.standard _) F inferInstance inferInstance inferInstance
  let qT := @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.standard _) T inferInstance inferInstance inferInstance
  let e : (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≅ L := by
    letI := hC
    letI := hD
    dsimp only [L, IntegralConstantModel.derived, Functor.asEquivalence]
    exact (qG.app P).symm ≪≫
      G.mapDerivedCategory.{u + 1, u + 2}.mapIso (Q.objObjPreimageIso K)
  let α := NatIso.mapHomologicalComplex (smallModulesSectionIso l E X) (.up ℤ)
  unfold ConstantCompletion.dres siteDerivedRestrictScalars smallDerivedObject
  exact (qF.app (DerivedCategory.Q.objPreimage L)).symm ≪≫
    F.mapDerivedCategory.{u + 2, u + 2}.mapIso (DerivedCategory.Q.objObjPreimageIso L) ≪≫
    F.mapDerivedCategory.{u + 2, u + 2}.mapIso e.symm ≪≫
    qF.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    (DerivedCategory.Q.mapIso (α.app P)) ≪≫
    (qT.app ((S.mapHomologicalComplex (.up ℤ)).obj P)).symm

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

/-- The completed realization tests the same extended residue ideal as the section
module presentation. No restriction functor, equivalence of complete categories, or
boundedness condition occurs in this comparison.

Source: blueprint integral-models, proof (1), coefficient identification; Stacks Tags
00YV, 099C and 099L.
(auxiliary; not a blueprint node).

Proof: identify the spectral and absolute integral coefficient rings by pointComparison.
The integral limit comparison and the normalized finite projection comparisons identify
the completed realization's first residue map with the first quotient of the reconstructed
continuous ring. The discrete residue kernel is the sheaf ideal generated by the constant
uniformizer: this follows from exact constant sheafification of O_E → O_E/(pi).
Its extension along the specified scalar map is therefore the continuous first-residue
kernel, since both quotients are the same residue sheaf. The section-action equivalence
and the equivalence of small sites restrict to each slice and identify scalar multiplication,
sheafified localization by a section, and derived internal Hom. Exactness identifies the
localized representatives with those of the derived realization. Consequently vanishing
of each local internal Hom in IsSfbAdicComplete is precisely vanishing for every section
of this extended ideal. The chosen representatives are related by the factorization
isomorphisms for exact derived functors, and vanishing is invariant under these
isomorphisms. This proves both implications for every unbounded complex, with the same
argument for zero objects and the empty scheme. -/
theorem integralModels_complete_section_predicate (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    let I := ConstantCompletion.kernelIdeal (smallMap X (residueMap l E X))
    let IB := I.extension (smallMap X (scalarMap l E X))
    Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
        ((IntegralConstantModel.derived l E X).functor.obj K) ↔
      IsLocallyDerivedRingedIdealComplete _ IB.module IB.inclusion
        (smallDerivedObject X _ K) := by
  let c := (Scheme.sfbModelRings X).map (completedSectionIso l E X).hom
  let q := (Scheme.sfbModelRings X).map
    (limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)) (op 0))
  let I := ConstantCompletion.kernelIdeal q
  have h := localComplete_iso _ I (derivedSectionIso l E X K)
  change Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K) ↔ _ at h
  have hr := siteDerivedRestrictScalars_locallyDerivedComplete_iff c I
    (smallDerivedObject X _ K)
  have hi := completedSectionIdeal l E X
  exact h.trans (hr.trans (by rw [hi]))

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
