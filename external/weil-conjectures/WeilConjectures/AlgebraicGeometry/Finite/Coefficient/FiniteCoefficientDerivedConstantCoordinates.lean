/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicLisseFixed
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-! # Constant complexes in fixed coordinates on an etale chart

Source: Stacks Project, Tags 03CY, 093J and 099R.
(blueprint: lem-weil-pbc-finite-coefficient-derived-constant-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

private def scalarCancelIso {C : Type (t + 1)} [Category.{t} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{t + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def scalarRestrictionEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] :
    SheafOfModules.{t + 1} ((adicLisseForget X).obj S) ≌
      SheafOfModules.{t + 1} ((adicLisseForget X).obj R) :=
  let e := (adicLisseForget X).mapIso (asIso φ)
  CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{t + 1} e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (scalarCancelIso e.inv e.hom e.inv_hom_id).symm
    (scalarCancelIso e.hom e.inv e.hom_inv_id)

private def derivedScalarCancellation (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] :
    completedAdicDerivedChange X φ ⋙ (pbcRestrict φ).mapDerivedCategory ≅ 𝟭 _ := by
  let E := scalarRestrictionEquivalence X φ
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let D := E.mapDerivedCategory
  let c : completedAdicDerivedChange X φ ≅ D.inverse :=
    (pbcDerivedScalarAdjunction φ).leftAdjointUniq D.symm.toAdjunction
  exact Functor.isoWhiskerRight c D.functor ≪≫ D.counitIso

private def fixedConstantComparison (X : Scheme.{t}) (B : Type t) [CommRing B] :
    constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} B)) ≅
      koszulConstantFunctor X B ⋙ proEtaleModuleRestriction X B := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have h (N : ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
    ConstantScalarComparison.constantComparisonHom_isIso
      (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
        (koszulConstantUnit X B) N
  refine NatIso.ofComponents (fun N ↦ asIso
    (ConstantScalarComparison.constantComparisonHom
      (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
        (koszulConstantUnit X B) N)) ?_
  intro N N' f
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((koszulConstantFunctor X B ⋙ proEtaleModuleRestriction X B).obj N').property
  let adj := PresheafOfModules.sheafificationAdjunction.{t + 1} (koszulConstantUnit X B)
  have hn := adj.unit.naturality ((siteConstantModulePresheafGeneral
    (C := X.ProEt) (ULift.{t + 1} B)).map f)
  let η (N : ModuleCat.{t + 1} (ULift.{t + 1} B)) :
      (Functor.const X.ProEtᵒᵖ).obj N ⟶
        ((proEtaleModuleRestriction X B).obj ((koszulConstantFunctor X B).obj N)).obj :=
    { app U := (adj.unit.app ((siteConstantModulePresheafGeneral
        (C := X.ProEt) (ULift.{t + 1} B)).obj N)).app U
      naturality _ _ f := by
        ext x
        exact ConcreteCategory.congr_hom
          ((adj.unit.app ((siteConstantModulePresheafGeneral
            (C := X.ProEt) (ULift.{t + 1} B)).obj N)).naturality f) x }
  have hfac (N : ModuleCat.{t + 1} (ULift.{t + 1} B)) :
      toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj N) ≫
        (ConstantScalarComparison.constantComparisonHom
          (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
            (koszulConstantUnit X B) N).hom = η N :=
    ((sheafificationAdjunction (ProEt.topology X)
      (ModuleCat.{t + 1} (ULift.{t + 1} B))).homEquiv
        ((Functor.const X.ProEtᵒᵖ).obj N)
        ((proEtaleModuleRestriction X B).obj ((koszulConstantFunctor X B).obj N))).apply_symm_apply
          (η N)
  change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj N) ≫
      sheafifyMap (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map f)) ≫
        (ConstantScalarComparison.constantComparisonHom
          (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
            (koszulConstantUnit X B) N').hom =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj N) ≫
        (ConstantScalarComparison.constantComparisonHom
          (ProEt.topology X) (ULift.{t + 1} B) (adicModuleRing X B)
            (koszulConstantUnit X B) N).hom) ≫
        ((koszulConstantFunctor X B ⋙ proEtaleModuleRestriction X B).map f).hom
  rw [← toSheafify_naturality, Category.assoc, hfac N', hfac N]
  ext U x
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) hn) x

/-- Fixed-coordinate restriction of a derived constant realization is the corresponding
constant complex on the chart. This applies to arbitrary unbounded complexes.

Source: Stacks Project, change of rings (03CY), module sheafification (093J),
and localization (099R).
(blueprint: lem-weil-pbc-finite-coefficient-derived-constant-coordinates).

Proof: scalar restriction along psi is an exact equivalence, with inverse restriction
along psi inverse. Its derived inverse is left adjoint to derived restriction.
Uniqueness of left adjoints identifies completedAdicDerivedChange with that inverse;
thus derived scalar extension followed by restriction is the identity. Restricting the
module-sheafification of a constant module to constant scalars gives its module-valued
constant sheaf. The natural comparison is induced by the sheafification unit and is
invertible because the scalar map is locally bijective. Apply it to each differential.
Finally localization preserves constant sheaves. The factors and composition
isomorphisms for exact derived functors identify this composite with the displayed
universe-lifted constant complex. No bounds, nonempty charts or nonzero ring are used. -/
theorem finiteCoefficient_derived_constant_coordinates
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) (hψ : IsIso ψ) (W : X.Etale)
    (F : DerivedCategory (ModuleCat.{t} B)) :
    Nonempty ((finiteCoefficientSliceRestriction X B R ψ W).mapDerivedCategory.obj
      ((completedAdicDerivedChange X ψ).obj ((finitePerfectAdicDerivedConstant X B).obj F)) ≅
      (constantSheaf (ProEt.topology W.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapDerivedCategory.obj
          ((finitePerfectAdicAlgebraLift B).obj F)) := by
  classical
  have := hψ
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let S := pbcRestrict ψ
  let E := proEtaleModuleRestriction X B
  let L := AlgebraicGeometry.ProEtale.localizationRestriction D W.hom inferInstance
  let C := koszulConstantFunctor X B
  let A := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have : E.IsEquivalence := proEtaleModuleRestriction_isEquivalence X B
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := { map_add := rfl }
  have : PreservesFiniteLimits L := by
    dsimp [L, AlgebraicGeometry.ProEtale.localizationRestriction]
    infer_instance
  have := (AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction
    D W.hom inferInstance).isLeftAdjoint
  have hc : C.Additive ∧ PreservesFiniteLimits C ∧ PreservesFiniteColimits C :=
    commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) (ULift.{t + 1} B)
  have := hc.1
  have := hc.2.1
  have := hc.2.2
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  let c : C ⋙ E ⋙ L ≅ constantSheaf (ProEt.topology W.left) D :=
    Functor.isoWhiskerRight (fixedConstantComparison X B).symm L ≪≫
      Functor.isoWhiskerLeft (constantSheaf (ProEt.topology X) D)
        (AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
          D W.hom inferInstance).symm ≪≫
      AlgebraicGeometry.ProEtale.constantSheafCompUpperStarIso D W.hom
  let J := (finitePerfectAdicDerivedConstant X B).obj F
  refine ⟨?_⟩
  exact (Functor.mapDerivedCategoryCompIso S (E ⋙ L)).symm.app
      ((completedAdicDerivedChange X ψ).obj J) ≪≫
    (E ⋙ L).mapDerivedCategory.mapIso ((derivedScalarCancellation X ψ).app J) ≪≫
    (E ⋙ L).mapDerivedCategory.mapIso ((Functor.mapDerivedCategoryCompIso A C).symm.app F) ≪≫
    (Functor.mapDerivedCategoryCompIso C (E ⋙ L)).app (A.mapDerivedCategory.obj F) ≪≫
    (Functor.mapDerivedCategoryNatIso c).app (A.mapDerivedCategory.obj F)

end AlgebraicGeometry.Scheme
