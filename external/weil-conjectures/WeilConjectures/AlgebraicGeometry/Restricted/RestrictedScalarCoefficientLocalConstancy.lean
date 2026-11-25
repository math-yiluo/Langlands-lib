/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Restricted.RestrictedScalarTensorCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # The restricted constant coefficient is a finite local system

## References

* Stacks Project, Tags 03CY, 03DA, 00YV and 06YU
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev coefficientModule (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (restrictedScalarRingMap T f))).obj
    (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T B)))

private noncomputable abbrev coefficientModel {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) :
    ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  (ModuleCat.restrictScalars (RingHom.ulift f)).obj
    (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B))

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestrictionIso (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Nonempty ((constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (coefficientModel f) ≅
        (proEtaleModuleRestriction T A).obj (coefficientModule T f)) := by
  let J := ProEt.topology T
  let M := coefficientModel f
  let F := (proEtaleModuleRestriction T A).obj (coefficientModule T f)
  let η := toSheafify J
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))
  let fl : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := RingHom.ulift f
  have hs (U : T.ProEtᵒᵖ) (r : ULift.{u + 1, u} A) :
      ((restrictedScalarRingMap T f).hom.app U)
        ((proEtaleModuleScalarUnit T A).app U r) = η.app U ((RingHom.ulift f) r) := by
    have h := toSheafify_naturality J
      ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom fl))
    exact (ConcreteCategory.congr_hom (congr_app h U) r).symm
  let α : (Functor.const T.ProEtᵒᵖ).obj M ⟶ F.obj :=
    { app U := by
        letI := (F.obj.obj U).isModule
        exact ModuleCat.ofHom (X := M) (Y := F.obj.obj U)
          { toFun := η.app U
            map_add' := map_add _
            map_smul' := fun r x ↦ by
              change ULift.{u + 1, u} B at x
              change (η.app U).hom (fl r * x) =
                ((restrictedScalarRingMap T f).hom.app U)
                  ((proEtaleModuleScalarUnit T A).app U r) *
                    (show (proEtaleConstantRing T B).obj.obj U from (η.app U).hom x)
              rw [hs, map_mul] }
      naturality {U V} g := by
        ext x
        exact ConcreteCategory.congr_hom (η.naturality g) x }
  have hi : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J η x y h
  have hs' : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J η x
  let ψ : (constantSheaf J (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M ⟶ F :=
    ⟨sheafifyLift J α F.property⟩
  have hfac : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj M) ≫ ψ.hom = α :=
    toSheafify_sheafifyLift J α F.property
  have hψi : Presheaf.IsLocallyInjective J ψ.hom := by
    rw [← Presheaf.comp_isLocallyInjective_iff J
      (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj M)), hfac]
    exact hi
  have hψs : Presheaf.IsLocallySurjective J ψ.hom := by
    rw [← Presheaf.comp_isLocallySurjective_iff J
      (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj M)), hfac]
    exact hs'
  have : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨hψi, hψs⟩
  exact ⟨asIso ψ⟩

private theorem constantModulePullback
    {T X : Scheme.{u}} (a : X ⟶ T) (R : Type (u + 1)) [CommRing R]
    (M : ModuleCat.{u + 1} R) :
    Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} R) a).obj
      ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} R)).obj M) ≅
        (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj M) := by
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ a
  let V := ⊤_ T.ProEt
  have hV : IsTerminal V := terminalIsTerminal
  let e := (((constantSheafAdj (ProEt.topology T) (ModuleCat.{u + 1} R) hV).comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) a)).ofNatIsoRight
      (G.sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{u + 1} R)
        (ProEt.topology T) (ProEt.topology X) (Opposite.op V))).leftAdjointUniq
          (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
            (hV.isTerminalObj G V))
  exact ⟨e.app M⟩

private theorem coefficientModule_lisse
    {T X : Scheme.{u}} (a : X ⟶ T)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B) :
    IsLocallyConstantProEtaleModuleSheaf X A
      (proEtaleConstantModulePullback a A (coefficientModule T f)) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
        (proEtaleConstantModulePullback a A (coefficientModule T f))) := by
  let R := ULift.{u + 1, u} A
  let M := coefficientModel f
  let F := proEtaleConstantModulePullback a A (coefficientModule T f)
  let F' := (proEtaleModuleRestriction X A).obj F
  let e : F' ≅ (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj M :=
    (proEtaleModuleRestriction_pullback a A (coefficientModule T f)).some ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} R) a).mapIso
      (coefficientRestrictionIso T f).some.symm ≪≫
    (constantModulePullback a R M).some
  have hconst : ProEtale.IsFiniteLocallyConstant R
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj M) := by
    refine ⟨PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X, ?_, fun _ ↦ ?_⟩
    · rw [Presieve.ofArrows_of_unique]
      exact Precoverage.mem_coverings_of_isIso (𝟙 X)
    · have : Finite M := inferInstanceAs (Finite (ULift.{u + 1, u} B))
      exact ⟨M, inferInstance,
        ⟨(constantModulePullback (𝟙 X) R M).some⟩⟩
  exact (finiteLocal_iff X A F).mp
    (ProEtale.isFiniteLocallyConstant_of_iso e.symm hconst)

/-- The restricted coefficient complex has finite locally constant cohomology after
arbitrary pullback. Its only possible nonzero cohomology is in degree zero. -/
theorem restrictedScalarCoefficient_finiteLocalConstancy
    {T X : Scheme.{u}} (a : X ⟶ T)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    (j : ℤ) :
    IsLocallyConstantProEtaleModuleSheaf X A
      (proEtaleConstantModulePullback a A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
            (DerivedCategory.Q.obj (restrictedScalarCoefficientComplex T f)))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
        (proEtaleConstantModulePullback a A
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
              (DerivedCategory.Q.obj (restrictedScalarCoefficientComplex T f))))) := by
  let L := restrictedScalarCoefficientComplex T f
  let E := proEtaleConstantModulePullbackFunctor a A
  by_cases hj : j = 0
  · subst j
    let e := E.mapIso ((DerivedCategory.homologyFunctorFactors _ 0).app L ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (coefficientModule T f))
    obtain ⟨hl, hs⟩ := coefficientModule_lisse a f
    refine ⟨locallyConstant_of_iso X A e.symm hl, fun Ω _ _ x ↦ ?_⟩
    let : Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
        (E.obj (coefficientModule T f))) := hs Ω x
    exact finite_stalk_of_iso X A e.symm x
  · have hz : IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
          (DerivedCategory.Q.obj L)) :=
      (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
        (coefficientModule T f) j hj).of_iso
          ((DerivedCategory.homologyFunctorFactors _ j).app L)
    have hz' := E.map_isZero hz
    exact ⟨locallyConstant_of_isZero X A _ hz', fun Ω _ _ x ↦
      finite_stalk_of_isZero X A _ hz' x⟩

end AlgebraicGeometry.Scheme
