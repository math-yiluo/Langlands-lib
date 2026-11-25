/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Ordinary homology of the finite constant tensor model

Source: Stacks Project, sites-cohomology.tex, Tags 094H and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

@[irreducible] private def restrictionCompIso (X : Scheme.{t})
    {R S T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ T) :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def restrictionIdIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    SheafOfModules.restrictScalars.{t + 1} (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

private theorem restrictionIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{t + 1} e.hom).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (SheafOfModules.restrictScalars e.inv)
  · exact (restrictionIdIso X S).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.inv_hom_id.symm) ≪≫
      restrictionCompIso X e.inv e.hom
  · exact (restrictionCompIso X e.hom e.inv).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.hom_inv_id) ≪≫
      restrictionIdIso X R

private theorem changeIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] : (completedAdicChange X φ).IsEquivalence := by
  let G := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  have : G.IsEquivalence := restrictionIsEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso (asIso φ))
  let a := (completedAdjunction X φ).choose
  exact a.isEquivalence_left_of_isEquivalence_right

@[irreducible] private def derivedChangeComplexIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ]
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ) :
    (completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := changeIsEquivalence X φ
  let F := completedAdicChange X φ
  let L := completedAdicDerivedChange X φ
  let ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose
  have : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.1
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  let i : L ≅ F.mapDerivedCategory :=
    Functor.leftDerivedNatIso L F.mapDerivedCategory ε F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  exact i.app _ ≪≫ F.mapDerivedCategoryFactors.app K

private abbrev baseConstantFunctor (X : Scheme.{t}) (B : Type t) [CommRing B] :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙ koszulConstantFunctor X B

private theorem baseConstantExact (X : Scheme.{t}) (B : Type t) [CommRing B] :
    (baseConstantFunctor X B).Additive ∧
      PreservesFiniteLimits (baseConstantFunctor X B) ∧
      PreservesFiniteColimits (baseConstantFunctor X B) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} B)
  have : (koszulConstantFunctor X B).Additive := h.1
  have : PreservesFiniteLimits (koszulConstantFunctor X B) := h.2.1
  have : PreservesFiniteColimits (koszulConstantFunctor X B) := h.2.2
  have : PreservesFiniteLimits (baseConstantFunctor X B) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (baseConstantFunctor X B) := comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

@[irreducible] private def modelHomologyIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) [IsIso φ]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((completedAdicDerivedChange X φ).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≅
      (finiteCoefficientConstantFunctor X B φ).obj (P.homology q) := by
  have := changeIsEquivalence X φ
  have := (baseConstantExact X B).1
  have := (baseConstantExact X B).2.1
  have := (baseConstantExact X B).2.2
  exact (DerivedCategory.homologyFunctor _ q).mapIso
      (derivedChangeComplexIso X φ (finiteModelConstantComplex X B P)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    ((finiteModelConstantComplex X B P).sc q).mapHomologyIso (completedAdicChange X φ) ≪≫
    (completedAdicChange X φ).mapIso ((P.sc q).mapHomologyIso (baseConstantFunctor X B))

/--
The homology of the derived constant realization of a tensor complex is the
ordinary constant realization of its algebraic homology when the coefficient
maps are isomorphisms.  This is the termwise homology calculation together
with transport along the coefficient isomorphism and restriction to the chart.

Source: Stacks Project, sites-cohomology.tex, Tag 094H (locally constant tensor
products) and Tag 06YU (bounded-above flat-complex calculation).
Proof: for the isomorphic coefficient map, the chosen derived change is
identified with ordinary scalar change.  Evaluate the constant realization
termwise and apply the canonical homology comparison for a mapped homological
complex.  Exact coefficient transport and chart over-restriction preserve the
resulting isomorphism with the ordinary homology of
`finiteQuotientLayerTensorComplex`.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification).
-/
theorem finiteQuotient_layer_tensor_model_homology_identification
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (q : ℤ) :
    Nonempty
      (((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X (φ (n + 1))).obj
              (DerivedCategory.Q.obj
                (finiteModelConstantComplex X _
                  (finiteQuotientLayerTensorComplex d.ideal n P)))))) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj
            ((finiteQuotientLayerTensorComplex d.ideal n P).homology q))) := by
  have : IsIso (φ (n + 1)) := hφ (n + 1)
  let e := modelHomologyIso X _ (φ (n + 1))
    (finiteQuotientLayerTensorComplex d.ideal n P) q
  exact ⟨(SheafOfModules.overFunctor _ ((toProEt X).obj Z)).mapIso e⟩

end AlgebraicGeometry.Scheme
