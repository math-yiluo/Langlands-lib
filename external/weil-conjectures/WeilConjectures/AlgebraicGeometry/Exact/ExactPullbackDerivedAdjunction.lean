/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Normalized derived adjunction for an exact module inverse image -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

/-- Exact module inverse image has a normalized unbounded derived adjunction.

Source: Stacks Project, Tag 07A6, lemma-adjoint, and Derived Categories,
Tags 08BJ, 070I and 070K (blueprint: lem-sp-exact-pullback-derived-adjunction).

Proof: module sheaves form a Grothendieck abelian category, hence admit K-injective
resolutions. On a K-injective target J, the right derived functor is computed by GJ.
Exactness of pull ensures that GJ is K-injective. The termwise adjunction descends
through chain homotopies and the two localization Hom bijections into K-injectives.
These bijections are natural, so they form an adjunction. The universal left-derived
comparison identifies its left adjoint with the specified derivedPull. Applying the
bijections to a chain map from pull(P) to J gives exactly the displayed normalization.
The K-flat and flat-term conditions ensure that its source comparison is invertible. -/
theorem exactPullbackDerivedAdjunction
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{u}} {S : Sheaf JD CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (G : Mod S ⥤+ Mod R) (aM : pull F c ⊣ G.obj)
    [PreservesFiniteLimits (pull F c)] [PreservesFiniteColimits (pull F c)] :
    ∃ (RF : D (S) ⥤ D (R))
        (ηG : G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q (R) ⟶
          Q (S) ⋙ RF),
        RF.IsRightDerivedFunctor ηG
            (HomologicalComplex.quasiIso (Mod (S)) (ComplexShape.up ℤ)) ∧
        (∀ J : Cx (S), J.IsKInjective → IsIso (ηG.app J)) ∧
        ∃ aD : (derivedPull F V adj (c)).functor ⊣ RF,
          (∀ (P : Cx (R)) (J : Cx (S)),
            P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → J.IsKInjective →
            ∀ f : ((pull F (c)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P ⟶ J,
              aD.homEquiv ((Q (R)).obj P) ((Q (S)).obj J)
                ((derivedPull F V adj (c)).comparison.app P ≫
                  (Q (S)).map f) =
                (Q (R)).map
                  ((aM.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P J f) ≫
                    ηG.app J) := by
  let : HasDerivedCategory (Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Mod S) := HasDerivedCategory.standard _
  have : IsGrothendieckAbelian.{u} (Mod S) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      JD S).1
  let H := G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q R
  let W := HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ)
  let W' := HomologicalComplex.quasiIso (Mod S) (ComplexShape.up ℤ)
  let Φ := CochainComplex.KInjectives.localizerMorphism (Mod S)
  have hd : Φ.Derives H := by
    intro K J f hf
    have : K.obj.IsKInjective := K.property
    have : J.obj.IsKInjective := J.property
    have hq : QuasiIso f.hom := hf
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
    have he' : HomologicalComplex.homotopyEquivalences (Mod R)
        (ComplexShape.up ℤ)
        ((G.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
      ⟨G.obj.mapHomotopyEquiv e, congrArg
        (G.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map he⟩
    have : QuasiIso ((G.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
      homotopyEquivalences_le_quasiIso _ _ _ he'
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      ((G.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom)))
  have := hd.hasPointwiseRightDerivedFunctor
  let RF := H.totalRightDerived (Q S) W'
  let β := H.totalRightDerivedUnit (Q S) W'
  have : RF.IsRightDerivedFunctor β W' := by
    dsimp only [RF, β]
    infer_instance
  have hβ : ∀ J : Cx S, J.IsKInjective → IsIso (β.app J) := by
    intro J hJ
    let : J.IsKInjective := hJ
    exact hd.isIso_of_isRightDerivedFunctor β (.mk J)
  let LF := (derivedPull F V adj c).functor
  let α := (derivedPull F V adj c).comparison
  have : LF.IsLeftDerivedFunctor α W := (derivedPull F V adj c).universal
  have hi : W.IsInvertedBy ((pull F c).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ Q S) := by
    intro P P' f hf
    have : QuasiIso f := hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      (((pull F c).mapHomologicalComplex (ComplexShape.up ℤ)).map f)))
  have : IsIso α := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LF α hi
  have : (LF ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso α) RF)
  have : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight β LF ≫ (Functor.associator _ _ _).hom) W' :=
    Φ.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun J ↦ hd.isIso_of_isRightDerivedFunctor β J) LF
  let ad := (aM.mapHomologicalComplex (ComplexShape.up ℤ)).derived W W' α β
  refine ⟨RF, β, inferInstance, hβ, ad, ?_⟩
  intro P J hP hflat hJ f
  change ad.homEquiv _ _ (α.app P ≫ (Q S).map f) = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change (((aM.mapHomologicalComplex (ComplexShape.up ℤ)).derivedη W α β).app
    ((Q R).obj P) ≫ RF.map (α.app P)) ≫ RF.map ((Q S).map f) = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := β.naturality f
  change (Q R).map ((G.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫ β.app J =
    β.app (((pull F c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      RF.map ((Q S).map f) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_unit]

end CategoryTheory.ConstantCompletion
