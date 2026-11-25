/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackComparison
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralLinePullIso
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Completed realization and normalized inverse image

Source: blueprint latest, sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3).
(blueprint: lem-sfb-diagonal-realization-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private def residueTower (l : ℕ) : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun n ↦ CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.toRingHom)))

private def residueTowerIso (l : ℕ) (X : Scheme.{u}) :
    Scheme.proEtaleCoefficientTower X (residueTower l) ≅ Scheme.purTwistZlTower X l :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ (NatTrans.ofOpSequence
      (F := Scheme.proEtaleCoefficientTower X (residueTower l))
      (G := Scheme.purTwistZlTower X l)
      (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp [Scheme.proEtaleCoefficientTower, residueTower, Scheme.purTwistZlTower,
          Scheme.purTwistZlTowerOfUniverses,
          Scheme.purTwistFiniteTransitionOfUniverses])).naturality f)

/-- The canonical completed coefficient comparison is invertible.
Source: blueprint coefficient changes (3)
(blueprint: lem-sfb-diagonal-realization-pullback).
Proof: the map is the limit lift of the finite constant-section comparisons.
Apply lem-weil-pbc-profinite-coefficient-inverse-image to the positive finite
coefficient tower. Its projection equations identify its comparison with this
limit lift, and its invertibility gives the assertion. -/
theorem diagonalRealization_coefficient_isIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsIso (diagonalCompletedCoefficientMap l f) := by
  let Q := residueTower.{u} l
  have (n : ℕᵒᵖ) : NeZero (l ^ (n.unop + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := by
    change Finite (ULift (ZMod (l ^ (n.unop + 1))))
    infer_instance
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (residueTowerIso l W)
  let L := Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}
  have := (Scheme.proEtale_profinite_coefficient_inverse_image Q).2.1 X S f
  let t := L.mapIso (c S).symm ≪≫
    asIso (Scheme.proEtaleProfiniteComparison f Q) ≪≫ c X
  suffices h : diagonalCompletedCoefficientMap l f = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [diagonalCompletedCoefficientMap, t, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (Scheme.proEtale_profinite_coefficient_inverse_image Q).2.2.1 X S f (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [residueTowerIso, Iso.trans_hom, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    Category.comp_id, Scheme.proEtaleConstantComparison]
  let p : L.obj (Scheme.purTwistZlCompletion S l) ⟶
      L.obj (Scheme.purTwistFiniteRing S l n) := L.map (Scheme.purTwistZlProjection S l n)
  let a : L.obj (Scheme.purTwistFiniteRing S l n) ⟶ Scheme.purTwistFiniteRing X l n :=
    Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  change p ≫ a = p ≫ L.map (𝟙 (Scheme.purTwistFiniteRing S l n)) ≫ a ≫
    𝟙 (Scheme.purTwistFiniteRing X l n)
  simp only [Category.comp_id]
  calc
    p ≫ a = p ≫ 𝟙 _ ≫ a := by rw [Category.id_comp]
    _ = p ≫ L.map (𝟙 (Scheme.purTwistFiniteRing S l n)) ≫ a :=
      (congrArg (fun z : L.obj (Scheme.purTwistFiniteRing S l n) ⟶
          L.obj (Scheme.purTwistFiniteRing S l n) ↦ p ≫ z ≫ a)
        (L.map_id (Scheme.purTwistFiniteRing S l n))).symm

attribute [instance] diagonalRealization_coefficient_isIso

/-- The actual sheafified tensor inverse image along the canonical completed
coefficient isomorphism; no completion is applied to its values.
Source: blueprint coefficient changes (3)
(blueprint: lem-sfb-diagonal-realization-pullback). -/
abbrev diagonalRealizationPull (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) : DiagonalCompleted l S ⥤ DiagonalCompleted l X :=
  Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
    (Scheme.purTwistZlCompletion X l) (asIso (diagonalCompletedCoefficientMap l f))

/-- The root-normalized inverse-image arrow, transported between the two specified
abelian inverse-image adjunctions through their common direct image.
Source: blueprint coefficient changes (3), integral Tate comparison
(blueprint: lem-sfb-diagonal-realization-pullback). -/
def diagonalRealizationLinePullMap (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (upperStar Ab.{u + 1} f).obj (zlLine l S).X ⟶ (zlLine l X).X :=
  ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
    ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
      (spIntegralComparison f l (bottomField l)))

/-- The completed endpoint in degree zero, using the exact single comparison.
Source: blueprint coefficient changes (3)
(blueprint: lem-sfb-diagonal-realization-pullback). -/
def diagonalRealizationPullSingle (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {M : DiagonalCompleted l S} {N : DiagonalCompleted l X}
    (t : (diagonalRealizationPull l f).obj M ≅ N) :
    (diagonalRealizationPull l f).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj M) ≅
        (DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).obj N :=
  (diagonalRealizationPull l f).mapDerivedCategorySingleFunctor 0 |>.app M |>.trans
    ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso t)

/-- The completed endpoint with its canonical cochain shift comparison.
Source: blueprint coefficient changes (3)
(blueprint: lem-sfb-diagonal-realization-pullback). -/
def diagonalRealizationPullShift (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {M : DiagonalCompleted l S} {N : DiagonalCompleted l X}
    (t : (diagonalRealizationPull l f).obj M ≅ N) (r : ℤ) :
    (diagonalRealizationPull l f).mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj M)⟦r⟧) ≅
        ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).obj N)⟦r⟧ :=
  ((diagonalRealizationPull l f).mapDerivedCategory.commShiftIso r).app _ ≪≫
    (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) r).mapIso
      (diagonalRealizationPullSingle l f t)

/-- All endpoint and arrow equations of the normalized realization square.
The line endpoint uses the actual root-limit comparison, and the derived functor
on condensed modules is the published derived inverse image.
Source: blueprint coefficient changes (3)
(blueprint: lem-sfb-diagonal-realization-pullback). -/
structure DiagonalRealizationPullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) where
  unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
    (zlLine l S) (zlLine l X) (diagonalRealizationLinePullMap l f)
  completedUnit : (diagonalRealizationPull l f).obj (SheafOfModules.unit
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))) ≅
      SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  completedLine : (diagonalRealizationPull l f).obj (Scheme.purTwistZlModule S l) ≅
    Scheme.purTwistZlModule X l
  completedUnit_normalization : ∀ (U : S.ProEtᵒᵖ)
      (a : (Scheme.purTwistZlCompletion S l).obj.obj U),
    ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l)
      (asIso (diagonalCompletedCoefficientMap l f))).homEquiv _ _
        completedUnit.hom).val.app U a =
      (Scheme.proEtaleRingDirectImageMap f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l)
        (asIso (diagonalCompletedCoefficientMap l f))).hom.app U a
  completedLine_normalization : ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (z : (Scheme.purTwistZlOne S l).obj.obj U),
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
      (((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l)
        (asIso (diagonalCompletedCoefficientMap l f))).homEquiv _ _
          completedLine.hom).val.app U z) =
      (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
        ((limit.π (Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))
          (op n)).hom.app U z)
  comparison : (diagonalRealizationPull l f).mapDerivedCategory ⋙ eX.F.mapDerivedCategory ≅
    eS.F.mapDerivedCategory ⋙ derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  shifts : NatTrans.CommShift comparison.hom ℤ
  unit_component : comparison.hom.app (DiagonalTrace.completedUnit l S) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.singleUnit l S) ≫ unit.derived =
    eX.F.mapDerivedCategory.map (diagonalRealizationPullSingle l f completedUnit).hom ≫
      eX.singleUnit l X
  line_component : comparison.hom.app ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map (diagonalRealizationPullShift l f completedLine 2).hom ≫
      eX.shiftedLine l X
  unit_unique : ∀ c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f,
    c.iso = unit.iso
  arrow : ∀ z : DiagonalTrace.completedUnit l S ⟶
      (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧,
    unit.derived ≫ eX.localChern l X
        ((diagonalRealizationPullSingle l f completedUnit).inv ≫
          (diagonalRealizationPull l f).mapDerivedCategory.map z ≫
            (diagonalRealizationPullShift l f completedLine 2).hom) =
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.localChern l S z) ≫ line.shift

private theorem realization_unit_endpoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) : Nonempty (UnitPullEndpoint Λ f) := by
  refine ⟨⟨(Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm, ?_⟩⟩
  exact CondensedRing.homEquiv_εIso_inv_hom Λ f

private theorem realization_endpoint_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (e : (CondensedRing.upperStar Λ f).obj M ≅ N)
    (h : (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ e.hom.hom = m) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N) e.hom).hom =
      (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X m := by
  have hn :
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N) e.hom).hom =
        (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ e.hom.hom) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} f).map e.hom.hom = _
    erw [(Scheme.proEtaleSheafDirectImage f Ab.{u + 1}).map_comp, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (lowerStar Ab.{u + 1} f).map e.hom.hom)
      (moduleUnit_forget_inv Λ f M).symm
  exact hn.trans (congrArg
    ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv M.X N.X) h)

private theorem realization_restricted_endpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ' S) (N : Modules Λ' X)
    (c : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ' S)).obj M ⟶
      (Mod.comap (condensedPullbackHom Λ' f)).obj N) [hc : IsIso c.hom] :
    ∃ e : (CondensedRing.upperStar Λ f).obj
        ((Mod.comap (coefficientMap a S)).obj M) ≅
          (Mod.comap (coefficientMap a X)).obj N,
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _) e.hom).hom =
        (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _ c.hom := by
  obtain ⟨d, hd⟩ := restrict_semilinear (upperStar Ab.{u + 1} f)
    (coefficientMap a S) (coefficientMap a X)
    (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f) M N c
  have : IsIso d.hom := hd.symm ▸ hc
  obtain ⟨e, he⟩ := ordinaryLift_iso f Λ _ _ d
  refine ⟨e, ?_⟩
  apply realization_endpoint_normalization Λ f _ _ _ e
  exact he.trans hd

private theorem realization_zl_endpoint (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    ∃ e : (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj
        (zlLine l S) ≅ zlLine l X,
      (((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _) e.hom).hom =
          (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv
            (zlLine l S).X (zlLine l X).X
            (spIntegralComparison f l (bottomField l)) := by
  obtain ⟨c, hc⟩ := integralModuleComparison_exists f l (bottomField l)
  have : IsIso c.hom := by
    rw [hc]
    exact nativeIntegralComparison_isIso f l (bottomField l)
  have h := realization_restricted_endpoint (integralMap l (bottomField l)) f
    (spIntegralTwist S l (bottomField l)) (spIntegralTwist X l (bottomField l)) c
  erw [hc] at h
  exact h

private theorem realization_line_endpoint (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤))) :
    Nonempty (PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X) (diagonalRealizationLinePullMap l f)) := by
  let residue (T : Scheme.{u}) (hu : IsUnit (l : Γ(T, ⊤))) :
      ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      let ψ := (T.residue x).hom.comp (T.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hu.map ψ).invertible
  let := residue X hX
  let := residue S hS
  obtain ⟨q, hq⟩ := realization_zl_endpoint l f
  refine ⟨⟨q, ?_⟩⟩
  unfold diagonalRealizationLinePullMap
  rw [Equiv.apply_symm_apply]
  exact hq

private theorem arrow_of_components
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (H : A ⥤ B) (F : B ⥤ C) (E : A ⥤ D) (P : D ⥤ C)
    (e : H ⋙ F ≅ E ⋙ P)
    {U L : A} {U' L' : B} {V W : D} {V' W' : C}
    (t₀ : H.obj U ≅ U') (t₁ : H.obj L ≅ L')
    (s₀ : E.obj U ≅ V) (s₀' : F.obj U' ≅ V')
    (s₁ : E.obj L ⟶ W) (s₁' : F.obj L' ⟶ W')
    (p₀ : P.obj V ⟶ V') (p₁ : P.obj W ⟶ W')
    (h₀ : e.hom.app U ≫ P.map s₀.hom ≫ p₀ = F.map t₀.hom ≫ s₀'.hom)
    (h₁ : e.hom.app L ≫ P.map s₁ ≫ p₁ = F.map t₁.hom ≫ s₁')
    (z : U ⟶ L) :
    p₀ ≫ s₀'.inv ≫ F.map (t₀.inv ≫ H.map z ≫ t₁.hom) ≫ s₁' =
      P.map (s₀.inv ≫ E.map z ≫ s₁) ≫ p₁ := by
  apply (cancel_epi (e.hom.app U ≫ P.map s₀.hom)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₀]
  simp only [Iso.hom_inv_id_assoc]
  rw [← F.map_comp_assoc, t₀.hom_inv_id, F.map_id, Category.id_comp]
  rw [← P.map_comp_assoc, s₀.hom_inv_id, P.map_id, Category.id_comp]
  have hn : F.map (H.map z) ≫ e.hom.app L =
      e.hom.app U ≫ P.map (E.map z) := e.hom.naturality z
  rw [← reassoc_of% hn]
  exact (congrArg (fun k ↦ F.map (H.map z) ≫ k) h₁).symm

-- Elaborating the derived endpoint comparison unfolds several exact-functor compositors.
/-- Exact completed realization commutes with inverse image, with the prescribed
unit and integral Tate-line endpoints, their shifts, and normalized arrows.

Source: blueprint latest, sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3).
(blueprint: lem-sfb-diagonal-realization-pullback).

Proof:
1. The canonical completed coefficient comparison is invertible by the
   coefficient theorem above; it defines the exact scalar-extension pullback.
2. The inverse strong-monoidal unit comparison has the required condensed
   adjoint normalization. For the line, restrict the whole integral comparison
   along the bottom-field inclusion and lift it through extension by the
   invertible coefficient comparison. The forgetful adjunction-unit formula
   gives its prescribed normalization.
3. Apply lem-sfb-diagonal-realization-pullback-endpoints to obtain the completed
   regular and whole-root endpoints with their adjoint projection equations.
4. Apply lem-sfb-diagonal-realization-pullback-derived to these endpoints and
   the supplied realizations. This gives the derived natural isomorphism,
   shift compatibility, and the two endpoint component equations.
5. Every normalized unit endpoint has the same underlying module adjoint.
   Faithfulness and the adjunction Hom bijection identify its isomorphism.
6. For the arrow equation, precompose with the invertible source comparison
   followed by pullback of the source realization. Substitute the unit component
   equation, cancel source isomorphisms, apply naturality, and substitute the
   line component equation. Unfolding localChern gives the required formula. -/
theorem diagonalRealization_pullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    Nonempty (DiagonalRealizationPullback l f eX eS) := by
  obtain ⟨unit⟩ := realization_unit_endpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  obtain ⟨line⟩ := realization_line_endpoint l f hX hS
  obtain ⟨d⟩ := diagonalRealization_pullback_endpoints l f
    (asIso (diagonalCompletedCoefficientMap l f)) rfl hX hS
  obtain ⟨c⟩ := diagonalRealization_pullback_comparison l f
    (asIso (diagonalCompletedCoefficientMap l f)) rfl hX hS eX eS unit line d
  refine ⟨{
    unit := unit
    line := line
    completedUnit := d.completedUnit
    completedLine := d.completedLine
    completedUnit_normalization := d.completedUnit_normalization
    completedLine_normalization := d.completedLine_normalization
    comparison := c.comparison
    shifts := c.shifts
    unit_component := c.unit_component
    line_component := c.line_component
    unit_unique := ?_
    arrow := ?_
  }⟩
  · intro q
    apply Iso.ext
    apply ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _).injective
    apply Mod.hom_ext
    exact q.normalization.trans unit.normalization.symm
  · intro z
    have : IsIso (eS.singleUnit l S) := by
      unfold CompletedRealization.singleUnit
      infer_instance
    have : IsIso (eX.singleUnit l X) := by
      unfold CompletedRealization.singleUnit
      infer_instance
    unfold CompletedRealization.localChern
    exact arrow_of_components (diagonalRealizationPull l f).mapDerivedCategory
      eX.F.mapDerivedCategory eS.F.mapDerivedCategory
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      c.comparison (diagonalRealizationPullSingle l f d.completedUnit)
      (diagonalRealizationPullShift l f d.completedLine 2)
      (asIso (eS.singleUnit l S)) (asIso (eX.singleUnit l X))
      (eS.shiftedLine l S) (eX.shiftedLine l X) unit.derived line.shift
      c.unit_component c.line_component z

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
