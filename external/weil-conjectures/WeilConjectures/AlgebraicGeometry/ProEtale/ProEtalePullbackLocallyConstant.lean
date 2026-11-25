/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Pullback of locally constant finite module sheaves

## References

* Stacks Project, Tag 093R, specialized to the small pro-etale topoi
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Pullback preserves the given finite constant module models on the base-changed cover.
The arrows to `ProEt.mk (𝟙 V)` are unique, hence are precisely the structure maps of the
base-changed objects. The conclusion retains the same modules `M i`, not just their sizes. -/
theorem proEtaleConstantModulePullback_locallyConstant
    {V X : Scheme.{u}} (f : V ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X A)))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (a : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
    (hcover : Presieve.ofArrows U a ∈ (ProEt.precoverage X).coverings _)
    (M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (hfinite : ∀ i : I, Finite (M i))
    (htrivial : ∀ i : I,
      Nonempty (F.over (U i) ≅ proEtaleConstantModuleSheafOver X A (U i) (M i))) :
    ∃ b : ∀ i : I, (proEtaleBaseChange f).obj (U i) ⟶ ProEt.mk (𝟙 V),
      Presieve.ofArrows (fun i : I ↦ (proEtaleBaseChange f).obj (U i)) b ∈
          (ProEt.precoverage V).coverings _ ∧
        (∀ i : I, Nonempty
          ((proEtaleConstantModulePullback f A F).over ((proEtaleBaseChange f).obj (U i)) ≅
            proEtaleConstantModuleSheafOver V A ((proEtaleBaseChange f).obj (U i)) (M i))) ∧
        IsLocallyConstantProEtaleModuleSheaf V A (proEtaleConstantModulePullback f A F) := by
  classical
  let Λ := ULift.{u + 1, u} A
  let D := ModuleCat.{u + 1} Λ
  let G := (proEtaleModuleRestriction X A).obj F
  have model (i : I) :
      Nonempty ((ProEtale.upperStar D (U i).hom).obj G ≅
        (constantSheaf (ProEt.topology (U i).left) D).obj (M i)) := by
    let R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
    let α := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit X A)
    have : Presheaf.IsLocallyInjective ((ProEt.topology X).over (U i)) α :=
      (proEtaleConstantRingUnit_over_locallyBijective X A (U i)).1
    have : Presheaf.IsLocallySurjective ((ProEt.topology X).over (U i)) α :=
      (proEtaleConstantRingUnit_over_locallyBijective X A (U i)).2
    let Q := ConstantScalarComparison.restriction ((ProEt.topology X).over (U i))
      Λ (R.over (U i)) α
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology X).over (U i)) Λ (R.over (U i)) α (M i)
    obtain ⟨e⟩ := htrivial i
    let c : G.over (U i) ≅
        (constantSheaf ((ProEt.topology X).over (U i)) D).obj (M i) :=
      Q.mapIso e ≪≫ (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology X).over (U i)) Λ (R.over (U i)) α (M i))).symm
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) D
    let r : E.functor.obj (G.over (U i)) ≅
        (ProEtale.localizationRestriction D (U i).hom (U i).prop).obj G :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    exact ⟨(ProEtale.upperStarIsoLocalizationRestriction D (U i).hom (U i).prop).app G ≪≫
      r.symm ≪≫ E.functor.mapIso c ≪≫
      ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
        ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) D
        (Over.mkIdTerminal (X := U i))).app (M i)⟩
  let W (i : I) := (proEtaleBaseChange f).obj (U i)
  let b (i : I) : W i ⟶ ProEt.mk (𝟙 V) :=
    MorphismProperty.Over.homMk (W i).hom (Category.comp_id _)
  have hb : Presieve.ofArrows W b ∈ (ProEt.precoverage V).coverings _ := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    have hU : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hcover
      have ha : (fun i ↦ (a i).left) = (fun i ↦ (U i).hom) := by
        funext i
        exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (a i))
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (a i).left) ∈
        proetalePrecoverage X at hcover
      rwa [ha] at hcover
    exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (U i).hom) hU f _
      (fun i ↦ pullback.fst (U i).hom f)
      (fun i ↦ (IsPullback.of_hasPullback (U i).hom f).flip)
  let H := (proEtaleModuleRestriction V A).obj (proEtaleConstantModulePullback f A F)
  obtain ⟨eH⟩ := proEtaleModuleRestriction_pullback f A F
  have fixed (i : I) : Nonempty (H.over (W i) ≅
      (constantSheaf ((ProEt.topology V).over (W i)) D).obj (M i)) := by
    obtain ⟨em⟩ := model i
    let p : (W i).left ⟶ (U i).left := pullback.fst (U i).hom f
    let q : (W i).left ⟶ V := (W i).hom
    have heq : q ≫ f = p ≫ (U i).hom := pullback.condition.symm
    let c : (ProEtale.upperStar D q).obj H ≅
        (constantSheaf (ProEt.topology (W i).left) D).obj (M i) :=
      (ProEtale.upperStar D q).mapIso eH ≪≫
      ((ProEtale.upperStarComp D q f).app G).symm ≪≫
      eqToIso (congrArg (fun g ↦ (ProEtale.upperStar D g).obj G) heq) ≪≫
      (ProEtale.upperStarComp D p (U i).hom).app G ≪≫
      (ProEtale.upperStar D p).mapIso em ≪≫
      (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology (U i).left) D)
        (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange p) D
          (ProEt.topology (U i).left) (ProEt.topology (W i).left)).symm).app (M i) ≪≫
      ((proEtaleBaseChange p).constantSheafsheafPullbackIso D
        (ProEt.topology (U i).left) (ProEt.topology (W i).left)
        (ProEt.isTerminalMkId (U i).left)
        ((ProEt.isTerminalMkId (U i).left).isTerminalObj (proEtaleBaseChange p) _)).app
          (M i)
    have : (ProEt.sliceEquiv V (W i)).inverse.IsDenseSubsite
        (ProEt.topology (W i).left) ((ProEt.topology V).over (W i)) :=
      ProEt.sliceDense V (W i)
    let E := (ProEt.sliceEquiv V (W i)).sheafCongr
      ((ProEt.topology V).over (W i)) (ProEt.topology (W i).left) D
    let r : E.functor.obj (H.over (W i)) ≅
        (ProEtale.localizationRestriction D (W i).hom (W i).prop).obj H :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    exact ⟨E.functor.preimageIso (r ≪≫
      ((ProEtale.upperStarIsoLocalizationRestriction D (W i).hom (W i).prop).app H).symm
      ≪≫ c ≪≫ (((ProEt.sliceEquiv V (W i)).constantSheafSheafCongrIso
        ((ProEt.topology V).over (W i)) (ProEt.topology (W i).left) D
        (Over.mkIdTerminal (X := W i))).app (M i)).symm)⟩
  have models (i : I) : Nonempty
      ((proEtaleConstantModulePullback f A F).over (W i) ≅
        proEtaleConstantModuleSheafOver V A (W i) (M i)) := by
    let R := (sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing V A)
    let α := Functor.whiskerLeft (Over.forget (W i)).op (proEtaleModuleScalarUnit V A)
    have : Presheaf.IsLocallyInjective ((ProEt.topology V).over (W i)) α :=
      (proEtaleConstantRingUnit_over_locallyBijective V A (W i)).1
    have : Presheaf.IsLocallySurjective ((ProEt.topology V).over (W i)) α :=
      (proEtaleConstantRingUnit_over_locallyBijective V A (W i)).2
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology V).over (W i)) Λ (R.over (W i)) α (M i)
    obtain ⟨e⟩ := fixed i
    exact ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology V).over (W i)) Λ (R.over (W i)) α).preimageIso
        (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
          ((ProEt.topology V).over (W i)) Λ (R.over (W i)) α (M i)))⟩
  exact ⟨b, hb, models, ⟨I, W, b, hb, fun i ↦ ⟨M i, models i⟩⟩⟩

end AlgebraicGeometry.Scheme
