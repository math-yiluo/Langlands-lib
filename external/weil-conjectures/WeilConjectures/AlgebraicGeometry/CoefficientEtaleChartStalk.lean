/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CoefficientFixedScalarsLocalModels
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Derived stalk of a supplied constant etale chart

Source: Stacks Project, Tags 03PT, 04EQ and 094G.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe u v w a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def overStalkIso
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [LocallySmall.{w} C] (p : J.Point.{w}) {U : C} (z : p.fiber.obj U)
    {A : Type*} [Category A] [HasColimitsOfSize.{w, w} A] :
    J.overPullback A U ⋙ (p.over z).sheafFiber ≅ p.sheafFiber := by
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence p.fiber z
  let F := e.functor ⋙ Over.forget (p.fiber.elementsMk U z)
  have : F.Initial := inferInstance
  have : HasColimitsOfShape (FunctorToTypes.fromOverFunctor p.fiber z).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (p.over z).fiber.Elementsᵒᵖ A)
  exact Functor.isoWhiskerLeft
    (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π p.fiber).op)
    (Functor.Final.colimIso F.op)

/-- Taking a geometric stalk of one supplied constant chart recovers its algebraic model.
Source: Stacks Project, Etale Cohomology, 03PT and 04EQ; Cohomology on Sites, 094G.
(auxiliary; not a blueprint node).

Proof: The lift t defines a point of the localized etale site over W. The forgetful
functor from pointed neighborhoods in the slice to pointed neighborhoods in X is initial:
given any pointed neighborhood, take its fibre product with W, using the fixed lift t.
The fibre product also gives common refinements of any two such choices. Thus restriction
to this slice does not change the stalk. Undoing AsSmall similarly does not change this
filtered colimit. The stalk of a constant module sheaf is the original module: the constant
presheaf has that colimit and sheafification preserves the stalk. This is natural in the
module and hence in each differential of M. Apply the exact slice stalk to the given
isomorphism and the termwise constant-stalk isomorphism, then descend at quasi-isomorphisms.
Composition of exact-functor localizations identifies the result with the specified
coefficientEtaleDerivedStalk. No boundedness, finiteness or Noetherianity is used. -/
theorem coefficient_etale_chart_stalk
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (W : smallModelComparisonEtaleSite.{u, v} X)
    (M : CochainComplex (ModuleCat.{max v (u + 1)} B) ℤ)
    (hM : CoefficientFixedLocalModel (smallModelComparisonEtaleTopology.{u, v} X) B K W M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (t : Spec (.of Ω) ⟶ (AsSmall.down.obj W : X.Etale).left)
    (ht : t ≫ (AsSmall.down.obj W : X.Etale).hom = x) :
    Nonempty (DerivedCategory.Q.obj M ≅ (coefficientEtaleDerivedStalk X B x).obj K) := by
  let e : X.Etale ≌ smallModelComparisonEtaleSite.{u, v} X := AsSmall.equiv
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let U : X.Etale := AsSmall.down.obj W
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite J X.smallEtaleTopology := by
    change (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      (AsSmall.down.inducedTopology X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  let G := (e.sheafCongr X.smallEtaleTopology J (ModuleCat.{max v (u + 1)} B)).inverse
  let ei := Over.postEquiv (X := U) e
  have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over U)
      (J.over (e.functor.obj U)) := by
    change (Over.post (X := U) e.functor).IsCocontinuous _ _
    infer_instance
  have : ei.inverse.IsCocontinuous (J.over (e.functor.obj U))
      (X.smallEtaleTopology.over U) := by
    change (Over.post (X := e.functor.obj U) e.inverse ⋙
      Over.map (e.unitIso.inv.app U)).IsCocontinuous _ _
    have : (Over.map (e.unitIso.inv.app U)).IsCocontinuous
        (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj U)))
        (X.smallEtaleTopology.over U) := by
      constructor
      intro A R hR
      change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
      rw [Sieve.overEquiv_functorPullback_map]
      exact hR
    exact isCocontinuous_comp _ _ (J.over (e.functor.obj U))
      (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj U)))
  have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj U))
      (X.smallEtaleTopology.over U) := ei.isDenseSubsite_inverse_of_isCocontinuous _ _
  have : HasWeakSheafify (X.smallEtaleTopology.over U)
      (ModuleCat.{max v (u + 1)} B) :=
    sfbSheafTensor_hasWeakSheafify.{u + 1, u, max v (u + 1) + 1, max v (u + 1)}
      (X.smallEtaleTopology.over U)
  let Gi : Sheaf (J.over W) (ModuleCat.{max v (u + 1)} B) ⥤
      Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{max v (u + 1)} B) :=
    ei.functor.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} B)
    (X.smallEtaleTopology.over U) (J.over (e.functor.obj U))
  have : Gi.IsEquivalence :=
    (ei.sheafCongr (X.smallEtaleTopology.over U) (J.over (e.functor.obj U))
      (ModuleCat.{max v (u + 1)} B)).isEquivalence_inverse
  have : G.Additive := ⟨by intro A D f g; ext V m; rfl⟩
  have : Gi.Additive := ⟨by intro A D f g; ext V m; rfl⟩
  let p := pointSmallEtale x
  let z : p.fiber.obj U := Over.homMk t ht
  let H := (p.over z).sheafFiber (A := ModuleCat.{max v (u + 1)} B)
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  have : HasColimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) := inferInstance
  have : AB5OfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} _
  have : HasBinaryBiproducts
      (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{max v (u + 1)} B)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : H.Additive :=
    @GrothendieckTopology.Point.sheafFiber_additive.{u, max v (u + 1), max v (u + 1) + 1,
      u, u + 1} _ _ _ (p.over z) (ModuleCat.{max v (u + 1)} B)
      (ModuleCat.moduleCategory.{max v (u + 1), max v (u + 1)} B)
      inferInstance inferInstance inferInstance inferInstance
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteColimits H := inferInstance
  let R := J.overPullback (ModuleCat.{max v (u + 1)} B) W
  let R0 := X.smallEtaleTopology.overPullback (ModuleCat.{max v (u + 1)} B) U
  let F := coefficientModelFixedScalars J B
  let T := Gi ⋙ H
  have hc : constantSheaf (J.over W) (ModuleCat.{max v (u + 1)} B) ⋙ T ≅
      𝟭 (ModuleCat.{max v (u + 1)} B) := by
    let c :
        (Functor.whiskeringLeft _ _ (ModuleCat.{max v (u + 1)} B)).obj ei.functor.op ⋙
          presheafToSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max v (u + 1)} B) ≅
        presheafToSheaf (J.over (e.functor.obj U)) (ModuleCat.{max v (u + 1)} B) ⋙ Gi :=
      ei.functor.pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{max v (u + 1)} B) (X.smallEtaleTopology.over U)
      (J.over (e.functor.obj U))
    let k : presheafToSheaf (X.smallEtaleTopology.over U)
        (ModuleCat.{max v (u + 1)} B) ⋙ H ≅
        (p.over z).presheafFiber :=
      ((sheafificationAdjunction (X.smallEtaleTopology.over U)
        (ModuleCat.{max v (u + 1)} B)).comp
          (p.over z).skyscraperSheafAdjunction).leftAdjointUniq
        (p.over z).skyscraperPresheafAdjunction
    exact Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (Functor.const _) c.symm) H ≪≫
      Functor.isoWhiskerLeft (Functor.const _) k ≪≫
      NatIso.ofComponents ((p.over z).presheafFiberConstIso)
        (fun f ↦ (p.over z).presheafFiberConstIso_hom_naturality f)
  have hr : R ⋙ Gi ≅ G ⋙ R0 :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have hs : F ⋙ R ⋙ T ≅ coefficientEtaleModuleStalk X B x :=
    Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight hr H ≪≫ Functor.isoWhiskerLeft G (overStalkIso p z))
  let := HasDerivedCategory.standard
    (ConstantCompletion.Mod (ConstantCompletion.constant J B))
  have : HasSheafify J (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian J _
  have : HasSheafify (J.over W) (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian (J.over W) _
  let := HasDerivedCategory.standard (Sheaf J (ModuleCat.{max v (u + 1)} B))
  let := HasDerivedCategory.standard (Sheaf (J.over W) (ModuleCat.{max v (u + 1)} B))
  have : PreservesFiniteLimits
      (constantSheaf (J.over W) (ModuleCat.{max v (u + 1)} B)) :=
    preservesFiniteLimits_constantSheaf _ _
  let dT : CoefficientFixedDerivedCategory (J.over W) B ⥤
      DerivedCategory (ModuleCat.{max v (u + 1)} B) := T.mapDerivedCategory
  obtain ⟨em⟩ := hM
  refine ⟨(?_ : (coefficientEtaleDerivedStalk X B x).obj K ≅
    DerivedCategory.Q.obj M).symm⟩
  exact ((Functor.mapDerivedCategoryNatIso hs).app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso F (R ⋙ T)).app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso R T).app (F.mapDerivedCategory.obj K)).symm ≪≫
    dT.mapIso em ≪≫
    dT.mapIso
      ((constantSheaf (J.over W)
        (ModuleCat.{max v (u + 1)} B)).mapDerivedCategoryFactors.app M).symm ≪≫
    (Functor.mapDerivedCategoryCompIso
      (constantSheaf (J.over W) (ModuleCat.{max v (u + 1)} B)) T).app
        (DerivedCategory.Q.obj M) ≪≫
    (Functor.mapDerivedCategoryNatIso hc).app (DerivedCategory.Q.obj M) ≪≫
    (Functor.mapDerivedCategoryIdIso (ModuleCat.{max v (u + 1)} B)).app _

end AlgebraicGeometry.Scheme
