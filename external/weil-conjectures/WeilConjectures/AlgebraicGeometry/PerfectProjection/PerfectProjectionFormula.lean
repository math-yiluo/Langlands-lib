/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.IdentityProjectionCompactification.ProjectionFormulaIdentityCompactification
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateSlicePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
meta import Mathlib.Lean.Meta.CongrTheorems
meta import Mathlib.Tactic.Set
meta import Mathlib.Util.TermReduce

/-!
# Perfect projection formula for completed coefficient reductions

The completed ring is presented as the limit of constant finite quotient sheaves.
The recorded finite-coefficient comparisons identify this presentation with the
continuous-functions presentation, including its quotient maps. Tensors and derived
categories are ordinary and uncompleted. Natural numbers index positive exponents n+1.

## References

* Stacks Project, Cohomology on Sites, Tags 0B56 and 0944, and More on Algebra, Tag 0657
* Stacks 098T
* Stacks 0944 and 093M
-/

@[expose] public noncomputable section

set_option Elab.async true
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
-- Avoid scanning the large representative tactic states for unused tactics.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 30000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 2000] CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape
  CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.PerfectProjection

set_option linter.flexible false in
/-- Cached existing site infrastructure for the completed-coefficient proofs. -/
theorem completedCommRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) CommRingCat.{u + 1} := inferInstance

set_option linter.flexible false in
/-- Cached existing site infrastructure for the completed-coefficient proofs. -/
theorem completedCommRingLimits (T : Scheme.{u}) :
    HasLimitsOfSize.{u + 1, u + 1} (Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  inferInstance

attribute [local instance 3000] completedCommRingWeakSheafify completedCommRingLimits

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option linter.flexible false in
/-- The recorded completed ring, in its constant finite-quotient presentation. -/
def ring (T : Scheme.{u}) := adicLisseCompletedRing T d.ideal

set_option linter.flexible false in
/-- The existing module category over this completed ring, at the mandated coefficient size. -/
abbrev modules (T : Scheme.{u}) := proEtaleRingModules T (ring d T)

set_option linter.flexible false in
/-- The ordinary localization of module complexes, with no completion condition. -/
abbrev derived (T : Scheme.{u}) := DerivedCategory (modules d T)

set_option linter.flexible false in
/-- The residue as an object of the ordinary derived category over the completed ring. -/
abbrev quotient (T : Scheme.{u}) (n : ℕ) : derived d T :=
  (DerivedCategory.singleFunctor (modules d T) 0).obj
    (CompletedConstantReduction.residue T d.ideal n)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option linter.flexible false in
/-- The projectionwise constant-ring comparison is a cone, including all tower arrows. -/
theorem coefficientCone_naturality {n m : ℕᵒᵖ} (a : n ⟶ m) :
    𝟙 ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)) ≫
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) m) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (m.unop + 1))) =
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))) ≫
      (adicLisseRingSystem X d.ideal).map a := by
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  change 𝟙 _ ≫ _ ≫ c.app m = (_ ≫ c.app n) ≫ _
  rw [Category.id_comp, Category.assoc, ← c.naturality]
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, limit.w]

set_option linter.flexible false in
/-- The actual inverse-limit comparison, characterized by its quotient projections. -/
def coefficientMap :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ⟶
      ring d X :=
  limit.lift (adicLisseRingSystem X d.ideal)
    { pt := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)
      π := { app := fun n ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
              (proEtaleConstantComparison f).app
                (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
             naturality := fun _ _ a ↦ coefficientCone_naturality d f a } }

set_option linter.flexible false in
/-- The specified comparison is invertible for the finite quotient tower. -/
theorem coefficientMap_isIso : IsIso (coefficientMap d f) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
    Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
      (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let c (T : Scheme.{u}) : proEtaleCoefficientTower T Q ⟶ adicLisseRingSystem T d.ideal :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [proEtaleCoefficientTower, Functor.comp_map, Q, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
  have hc (T : Scheme.{u}) : IsIso (c T) := by
    have : ∀ n, IsIso ((c T).app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
    exact NatIso.isIso_of_isIso_app _
  have : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  have hp := proEtale_profinite_coefficient_inverse_image Q
  have := hp.2.1 X Y f
  have := hc X
  have := hc Y
  have he : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f = proEtaleProfiniteComparison f Q ≫ limMap (c X) := by
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, coefficientMap, limit.lift_π,
      limMap_π]
    change _ ≫ _ ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, limMap_π]
    simp only [c, NatTrans.ofOpSequence_app, Category.comp_id]
    exact (hp.2.2.1 X Y f n).symm
  have : IsIso ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)))
    (coefficientMap d f)

set_option linter.flexible false in
/-- The canonical coefficient identification; only its invertibility is postponed. -/
def coefficients :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ≅
      ring d X :=
  @asIso _ _ _ _ (coefficientMap d f) (coefficientMap_isIso d f)

set_option linter.flexible false in
/-- The ordinary derived pullback with this specific completed coefficient identification. -/
abbrev pullback :=
  proEtaleRingDerivedPullback f (ring d Y) (ring d X) (coefficients d f)

set_option linter.flexible false in
/-- The ordinary derived direct image with the same coefficient action. -/
abbrev directImage :=
  proEtaleRingDerivedDirectImage f (ring d Y) (ring d X) (coefficients d f)

variable (aY : ProEtaleTensorModel Y (ring d Y))
  (aX : ProEtaleTensorModel X (ring d X))
  (K : derived d X)

set_option linter.flexible false in
/-- The existing canonical projection mate, with the completed coefficients specialized. -/
abbrev projection (P : derived d Y) :=
  proEtaleProjectionFormulaMate f (ring d Y) (ring d X)
    (coefficients d f) aY aX K P

set_option linter.flexible false in
/-- The full isomorphism locus of the specified projection morphism. -/
def locus : ObjectProperty (derived d Y) :=
  fun P ↦ IsIso (projection d f aY aX K P)

attribute [local irreducible] coefficients SheafOfModules.monoidalClosed_kfg
  SheafOfModules.monoidalCategory
  CategoryTheory.tensorAdjunctionTotalInverse CategoryTheory.tensorAdjunctionTotal

set_option linter.flexible false in
private theorem strictPerfect_mem
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (F G : DerivedCategory C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (B : C) (hB : τ.isoLocus ((DerivedCategory.singleFunctor C 0).obj B))
    (T : CochainComplex C ℤ) (lo hi : ℤ)
    (hb : ∀ n : ℤ, n < lo ∨ hi < n → IsZero (T.X n))
    (rank : ℤ → ℕ) (i : ∀ n, T.X n ⟶ ∏ᶜ fun _ : Fin (rank n) ↦ B)
    (p : ∀ n, (∏ᶜ fun _ : Fin (rank n) ↦ B) ⟶ T.X n)
    (split : ∀ n, i n ≫ p n = 𝟙 _) :
    τ.isoLocus (DerivedCategory.Q.obj T) := by
  let H := DerivedCategory.singleFunctor C 0
  apply CategoryTheory.bounded_complex_mem_triangulated τ.isoLocus T lo hi hb
  intro n _ _
  have hfree : τ.isoLocus (H.obj (∏ᶜ fun _ : Fin (rank n) ↦ B)) :=
    τ.isoLocus.prop_of_isLimit
      (isLimitOfPreserves H (limit.isLimit
        (Discrete.functor (fun _ : Fin (rank n) ↦ B)))) (fun _ ↦ hB)
  exact τ.isoLocus.prop_of_retract ((show Retract (T.X n)
    (∏ᶜ fun _ : Fin (rank n) ↦ B) from ⟨i n, p n, split n⟩).map H) hfree

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Thick closure, the finite-free base case (including rank zero), and site-perfectness. -/
theorem perfect_projection_formula :
    (locus d f aY aX K).IsTriangulated ∧
    (locus d f aY aX K).IsStableUnderRetracts ∧
    (∀ m : ℕ, locus d f aY aX K
      ((DerivedCategory.singleFunctor (modules d Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj
          (ring d Y))))) ∧
    (∀ P : derived d Y,
      SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) P →
        locus d f aY aX K P) := by
  classical
  let (U : Y.ProEt) : HasDerivedCategory (SheafOfModules.{u + 1}
      (((adicLisseForget Y).obj (ring d Y)).over U)) := HasDerivedCategory.standard _
  obtain ⟨sF, sG, hF, hG, τ, hτ, hs, hu⟩ :=
    proEtaleProjectionMateExact f (ring d Y) (ring d X) (coefficients d f) aY aX K
  let := sF
  let := sG
  have := hF
  have := hG
  have := hs
  have hlocus : locus d f aY aX K = τ.isoLocus := by
    funext P
    exact congrArg IsIso (hτ P).symm
  rw [hlocus]
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro m
    exact τ.isoLocus.prop_of_isLimit
      (isLimitOfPreserves (DerivedCategory.singleFunctor (modules d Y) 0)
        (limit.isLimit (Discrete.functor (fun _ : Fin m ↦
          SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))))) (fun _ ↦ hu)
  · intro P hP
    obtain ⟨T, hT, ⟨e⟩⟩ := hP
    rw [NatTrans.isoLocus]
    rw [hτ P]
    apply SheafOfModules.ringedRestrictionLocalIso
      ((adicLisseForget Y).obj (ring d Y))
    intro V
    obtain ⟨S, hS, hlocal⟩ := hT V
    refine ⟨S, hS, ?_⟩
    intro U q hq
    obtain ⟨B, ⟨lo, hi, hb⟩, ⟨pkg⟩, z, hz⟩ := hlocal U q hq
    have := hz
    let R := ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2}
      ((adicLisseForget Y).obj (ring d Y)) U
    let L := SheafOfModules.overFunctor.{u + 1}
      ((adicLisseForget Y).obj (ring d Y)) U
    have : L.Additive := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).1
    have : PreservesFiniteLimits L :=
      (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).2.1
    have : PreservesFiniteColimits L :=
      (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).2.2
    let model : R.obj P ≅ DerivedCategory.Q.obj B :=
      R.mapIso e ≪≫ L.mapDerivedCategoryFactors.app T ≪≫
        (asIso (DerivedCategory.Q.map z)).symm
    obtain ⟨loc⟩ := proEtaleProjectionMateSlicePresentation f
      (ring d Y) (ring d X) (coefficients d f) aY aX K U
    let := loc.sourceShift
    let := loc.targetShift
    have := loc.sourceExact
    have := loc.targetExact
    have := loc.shiftCompatible
    let one := (DerivedCategory.singleFunctor (modules d Y) 0).obj
      (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
    have hunit : IsIso (proEtaleProjectionFormulaMate f (ring d Y) (ring d X)
        (coefficients d f) aY aX K one) := (congrArg IsIso (hτ one)).mp hu
    have hlocalunit : IsIso (loc.mate.app (R.obj one)) := by
      have : IsIso (loc.sourceComparison.hom.app one ≫
          loc.mate.app (R.obj one)) := by
        rw [← loc.equation one]
        infer_instance
      exact IsIso.of_isIso_comp_left (loc.sourceComparison.hom.app one) _
    let unitIso : R.obj one ≅ (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U)) :=
      (L.mapDerivedCategorySingleFunctor 0).app
        (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
    have hunit' : IsIso (loc.mate.app ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U)))) :=
      (NatTrans.isIso_app_iff_of_iso loc.mate unitIso).mp hlocalunit
    have hB := strictPerfect_mem loc.source loc.target loc.mate _ hunit'
      B lo hi hb pkg.N pkg.i pkg.p pkg.splitting
    have : IsIso (loc.mate.app (R.obj P)) :=
      (NatTrans.isIso_app_iff_of_iso loc.mate model).mpr hB
    have : IsIso (R.map (projection d f aY aX K P) ≫
        loc.targetComparison.hom.app P) := by
      rw [loc.equation P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (loc.targetComparison.hom.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem moduleUnit_existsUnique
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    ∃! j : (proEtaleRingModulePullback f R S c).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≅
          SheafOfModules.unit ((adicLisseForget X).obj S),
      ∀ (U : Y.ProEtᵒᵖ) (r : R.obj.obj U),
        ((proEtaleRingModuleAdjunction f R S c).homEquiv
          _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f R S c).hom.app U r := by
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (adicLisseForget Y).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((adicLisseForget X).obj S) :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj'.homEquiv _ _ (SheafOfModules.pullbackObjUnitToUnit φ) = _
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  refine ⟨j, ?_, ?_⟩
  · intro U r
    exact congrArg (fun z ↦ z.val.app U r) hj
  · intro j' hj'
    apply Iso.ext
    apply (adj.homEquiv _ _).injective
    rw [hj]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact hj' U r

set_option linter.flexible false in
private theorem restrictedUnit_existsUnique
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aY : R ⟶ RY) (aX : S ⟶ RX)
    (c0 : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (hc : c0.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ c.hom) :
    ∃! e : (proEtaleRingModulePullback f R S c0).obj
        ((proEtaleRingRestrictScalars aY).obj
          (SheafOfModules.unit ((adicLisseForget Y).obj RY))) ≅
        (proEtaleRingRestrictScalars aX).obj
          (SheafOfModules.unit ((adicLisseForget X).obj RX)),
      ∀ (U : Y.ProEtᵒᵖ) (x : RY.obj.obj U),
        ((proEtaleRingModuleAdjunction f R S c0).homEquiv _ _ e.hom).val.app U x =
          (proEtaleRingDirectImageMap f RY RX c).hom.app U x := by
  let resY := proEtaleRingRestrictScalars aY
  let resX := proEtaleRingRestrictScalars aX
  let adj := proEtaleRingModuleAdjunction f R S c0
  let adj' := proEtaleRingModuleAdjunction f RY RX c
  let cmp := proEtaleRingRestrictionDirectImage f R RY S RX
    aY aX c0 c hc
  let t := proEtaleRingRestrictionPullbackInv f R RY S RX
    aY aX c0 c hc
  have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso
    f R RY S RX aY aX c0 c hc
  obtain ⟨j, hj, _⟩ := moduleUnit_existsUnique f RY RX c
  let M := SheafOfModules.unit ((adicLisseForget Y).obj RY)
  let e : (proEtaleRingModulePullback f R S
      c0).obj ((proEtaleRingRestrictScalars aY).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj RY))) ≅
        (proEtaleRingRestrictScalars aX).obj
          (SheafOfModules.unit ((adicLisseForget X).obj RX)) :=
    (asIso t).app M ≪≫ resX.mapIso j
  have he : adj.homEquiv _ _ e.hom =
      resY.map (adj'.homEquiv _ _ j.hom) ≫
        cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX)) := by
    change adj.homEquiv _ _ (t.app M ≫ resX.map j.hom) = _
    have hh := mate_adjunct adj' adj (TwoSquare.mk _ _ _ _ t) M _ j.hom
    have hm := congrArg (fun q ↦ q.app
      (SheafOfModules.unit ((adicLisseForget X).obj RX)))
        (restrictionPullback_mate f R RY S RX aY aX c0 c hc)
    change (mateEquiv adj' adj (TwoSquare.mk _ _ _ _ t)).app _ = cmp.hom.app _ at hm
    rw [hm] at hh
    exact hh
  have he' : ∀ (U : Y.ProEtᵒᵖ)
      (x : RY.obj.obj U),
      (adj.homEquiv _ _ e.hom).val.app U x =
        (proEtaleRingDirectImageMap f RY RX c).hom.app U x := by
    intro U x
    rw [he]
    change (cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX))).val.app U
      ((adj'.homEquiv _ _ j.hom).val.app U x) = _
    erw [(Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique f R RY S RX
        aY aX c0 c hc)).1]
    exact hj U x
  refine ⟨e, he', ?_⟩
  intro e' he''
  apply Iso.ext
  apply (adj.homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (he'' U x).trans (he' U x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
/-- The canonical module pullback comparison is fixed by the constant-section adjunct. -/
theorem quotientPullback_existsUnique (n : ℕ) :
    ∃! e : (proEtaleRingModulePullback f (ring d Y) (ring d X)
        (coefficients d f)).obj (CompletedConstantReduction.residue Y d.ideal n) ≅
          CompletedConstantReduction.residue X d.ideal n,
      ∀ (U : Y.ProEtᵒᵖ)
        (x : (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))).obj.obj U),
        ((proEtaleRingModuleAdjunction f (ring d Y) (ring d X)
          (coefficients d f)).homEquiv _ _ e.hom).val.app U x =
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app
          (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))) ≫
          (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison f).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).hom.app U) x := by
  let RY := adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))
  let RX := adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))
  have : IsIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) := by
    let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n
    exact (proEtale_profinite_coefficient_inverse_image Q).1 X Y f (op n)
  let c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX :=
    asIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
  let aY : ring d Y ⟶ RY := limit.π (adicLisseRingSystem Y d.ideal) (op n)
  let aX : ring d X ⟶ RX := limit.π (adicLisseRingSystem X d.ideal) (op n)
  have hc : (coefficients d f).hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ c.hom := by
    unfold coefficients
    exact limit.lift_π _ (op n)
  exact restrictedUnit_existsUnique f (ring d Y) (ring d X) RY RX aY aX
    (coefficients d f) c hc

set_option linter.flexible false in
/-- Pull back the quotient module by its uniquely normalized module comparison. -/
def quotientPullback (n : ℕ) :=
  (quotientPullback_existsUnique d f n).exists.choose

set_option linter.flexible false in
/-- The derived comparison is the exact termwise pullback comparison in degree zero. -/
def quotientDerivedPullback (n : ℕ) :
    (pullback d f).obj (quotient d Y n) ≅ quotient d X n :=
  ((proEtaleRingModulePullback f (ring d Y) (ring d X)
    (coefficients d f)).mapDerivedCategorySingleFunctor 0).app
      (CompletedConstantReduction.residue Y d.ideal n) ≪≫
    (DerivedCategory.singleFunctor (modules d X) 0).mapIso (quotientPullback d f n)

set_option linter.flexible false in
/-- K_n as an A_X-object: derived tensor with the restricted quotient sheaf. -/
abbrev reduction (n : ℕ) := aX.tensor.obj (K, quotient d X n)

set_option linter.flexible false in
/-- The reduction projection map uses the canonical quotient pullback identification. -/
def reductionMap (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ⟶
      (directImage d f).obj (reduction d aX K n) :=
  projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))

/-- Chosen representatives for evaluating the signed-totalization inverse at a quotient.
The maps represent the fixed K and the fixed quotient, rather than new derived objects. -/
structure Resolution (n : ℕ) where
  injective : CochainComplex (modules d X) ℤ
  isKInjective : injective.IsKInjective
  representsK : K ≅ DerivedCategory.Q.obj injective
  coefficient : CochainComplex (modules d Y) ℤ
  bounded : ∃ l r : ℤ, ∀ i : ℤ, i < l ∨ r < i → IsZero (coefficient.X i)
  package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((adicLisseForget Y).obj (ring d Y)) coefficient
  representsQuotient : DerivedCategory.Q.obj coefficient ≅ quotient d Y n

set_option linter.flexible false in
set_option cleanup.letToHave true in
/-- Every quotient admits the representatives used in the totalization comparison. -/
theorem resolution_exists (n : ℕ) : Nonempty (Resolution d (X := X) (Y := Y) K n) := by
  classical
  have : IsNoetherianRing A := d.noetherian
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ := d.quotientPerfect (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have := ha
  have := hb
  have (i : ℤ) : Module.Projective A (F.X i) := (hF i).1
  have (i : ℤ) : Projective (F.X i) := inferInstance
  let Q := (CochainComplex.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))
  obtain ⟨q, hq⟩ := DerivedCategory.Q_map_surjective_of_projective F Q b eF.inv
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  have hq' : QuasiIso q :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u + 1} A) q).mp inferInstance
  have hbound : ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    intro i hi
    rcases hi with hi | hi
    · exact F.isZero_of_isStrictlyGE a i hi
    · exact F.isZero_of_isStrictlyLE b i hi
  obtain ⟨hred, hret, hbounded⟩ :=
    (CompletedConstantReduction.completed_constant_sheaf_reduction Y d.ideal).2.2.2
      n F q a b hq' (fun i ↦ ⟨(hF i).2, (hF i).1⟩) hbound
  let C : CochainComplex (modules d Y) ℤ := ((completedAdicChange Y
    (CompletedConstantReduction.base Y d.ideal)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex Y A).obj F)
  have : HasFiniteBiproducts (modules d Y) := HasFiniteBiproducts.of_hasFiniteProducts
  choose N i p hip using hret
  let e (j : ℤ) := biproductIso (fun _ : Fin (N j) ↦
    SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget Y).obj (ring d Y)) C :=
    { N := N
      i := fun j ↦ i j ≫ (e j).inv
      p := fun j ↦ (e j).hom ≫ p j
      splitting := fun j ↦ by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hip]
        rfl }
  let q' := CompletedConstantReduction.reductionComplex Y d.ideal n
    ((CompletedConstantReduction.constantComplex Y A).obj F)
    (CompletedConstantReduction.constantAugmentation Y d.ideal n F q)
  have : QuasiIso q' := hred
  let eq : DerivedCategory.Q.obj C ≅ quotient d Y n :=
    asIso (DerivedCategory.Q.map q')
  exact ⟨⟨I, hI, eI, C, ⟨a, b, hbounded⟩, pkg, eq⟩⟩

set_option linter.flexible false in
/-- Every positive quotient is site-perfect and its canonical projection map is invertible. -/
theorem reductionMap_isIso (n : ℕ) :
    SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) ∧
      IsIso (reductionMap d f aY aX K n) := by
  obtain ⟨r⟩ := resolution_exists d (X := X) (Y := Y) K n
  have hperfect : SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) := by
    refine ⟨r.coefficient, ?_, ⟨r.representsQuotient.symm⟩⟩
    intro V
    refine ⟨⊤, (ProEt.topology Y).top_mem V, ?_⟩
    intro U g _
    let L := SheafOfModules.overFunctor ((adicLisseForget Y).obj (ring d Y)) U
    have : PreservesFiniteLimits L :=
      (ringedOverFunctor_exactGeneral ((adicLisseForget Y).obj (ring d Y)) U).2.1
    let e (m : ℕ) :
        L.obj (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
          ∏ᶜ fun _ : Fin m ↦
            SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U) :=
      PreservesProduct.iso L _
    let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        (((adicLisseForget Y).obj (ring d Y)).over U)
        ((L.mapHomologicalComplex (.up ℤ)).obj r.coefficient) :=
      { N := r.package.N
        i := fun i ↦ L.map (r.package.i i) ≫ (e (r.package.N i)).hom
        p := fun i ↦ (e (r.package.N i)).inv ≫ L.map (r.package.p i)
        splitting := fun i ↦ by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp,
            r.package.splitting, L.map_id]
          rfl }
    refine ⟨(L.mapHomologicalComplex (.up ℤ)).obj r.coefficient, ?_, ⟨pkg⟩, 𝟙 _, ?_⟩
    · obtain ⟨a, b, hab⟩ := r.bounded
      exact ⟨a, b, fun i hi ↦ L.map_isZero (hab i hi)⟩
    · infer_instance
  refine ⟨hperfect, ?_⟩
  have : IsIso (projection d f aY aX K (quotient d Y n)) :=
    (perfect_projection_formula d f aY aX K).2.2.2 _ hperfect
  change IsIso (projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n))).hom)
  infer_instance

set_option linter.flexible false in
/-- The specified pi_n as an isomorphism, with the original projection map as its hom. -/
def reductionIso (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ≅
      (directImage d f).obj (reduction d aX K n) :=
  @asIso _ _ _ _ (reductionMap d f aY aX K n)
    (reductionMap_isIso d f aY aX K n).2

set_option linter.flexible false in
/-- rho_n is the unique inverse of the canonical, resolution-independent projection map. -/
abbrev inverse (n : ℕ) := (reductionIso d f aY aX K n).inv

set_option linter.flexible false in
/-- The actual quotient homomorphism is linear for the completed coefficient action. -/
theorem quotientModuleMap_existsUnique (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    ∃! q : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n,
      ∀ (U : T.ProEtᵒᵖ)
        (x : (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U),
        q.val.app U x =
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op).hom.app U x := by
  let q := (adicLisseRingSystem T d.ideal).map (homOfLE h).op
  let φ : (CompletedConstantReduction.residue T d.ideal m).val.presheaf ⟶
      (CompletedConstantReduction.residue T d.ideal n).val.presheaf :=
    Functor.whiskerRight q.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let qm : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n :=
    ⟨PresheafOfModules.homMk φ (by
      intro U r x
      change (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U at x
      change q.hom.app U
          ((show (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U from
            (limit.π (adicLisseRingSystem T d.ideal) (op m)).hom.app U r) * x) =
        (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
          (limit.π (adicLisseRingSystem T d.ideal) (op n)).hom.app U r) *
            (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
              q.hom.app U x)
      rw [map_mul]
      congr 1
      exact congrArg (fun z ↦ z.hom.app U r)
        (limit.w (adicLisseRingSystem T d.ideal) (homOfLE h).op))⟩
  refine ⟨qm, fun _ _ ↦ rfl, ?_⟩
  intro qm' hqm'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hqm' U x

set_option linter.flexible false in
/-- The quotient tower map retains its uniquely specified sectionwise quotient formula. -/
def quotientModuleMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :=
  (quotientModuleMap_existsUnique d T n m h).exists.choose

set_option linter.flexible false in
/-- The positive quotient tower map in the ordinary completed-coefficient derived category. -/
def quotientMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    quotient d T m ⟶ quotient d T n :=
  (DerivedCategory.singleFunctor (modules d T) 0).map (quotientModuleMap d T n m h)

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient pullback comparisons commute with every quotient tower map. -/
theorem quotientDerivedPullback_naturality (n m : ℕ) (h : n ≤ m) :
    (pullback d f).map (quotientMap d Y n m h) ≫ (quotientDerivedPullback d f n).hom =
      (quotientDerivedPullback d f m).hom ≫ quotientMap d X n m h := by
  let L := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)
  let adj := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let adjR := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  have hr := congrArg (adjR.homEquiv _ _) (c.naturality (homOfLE h).op)
  simp only [Functor.comp_map, adjR.homEquiv_naturality_left,
    adjR.homEquiv_naturality_right] at hr
  have hm : L.map (quotientModuleMap d Y n m h) ≫ (quotientPullback d f n).hom =
      (quotientPullback d f m).hom ≫ quotientModuleMap d X n m h := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (adj.homEquiv _ _ (quotientPullback d f n).hom).val.app U
        ((quotientModuleMap d Y n m h).val.app U x) =
      (quotientModuleMap d X n m h).val.app ((proEtaleBaseChange f).op.obj U)
        ((adj.homEquiv _ _ (quotientPullback d f m).hom).val.app U x)
    dsimp only [quotientModuleMap, quotientPullback, adj]
    rw [(quotientModuleMap_existsUnique d Y n m h).exists.choose_spec,
      (quotientPullback_existsUnique d f n).exists.choose_spec,
      (quotientPullback_existsUnique d f m).exists.choose_spec,
      (quotientModuleMap_existsUnique d X n m h).exists.choose_spec]
    exact congrArg (fun z ↦ z.hom.app U x) hr
  have hn := (L.mapDerivedCategorySingleFunctor 0).hom.naturality
    (quotientModuleMap d Y n m h)
  change (pullback d f).map (quotientMap d Y n m h) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f n).hom =
    ((L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f m).hom) ≫ _
  dsimp only [Functor.comp_map] at hn
  dsimp only [pullback, proEtaleRingDerivedPullback, quotientMap]
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp, hm]

set_option linter.flexible false in
private theorem inverse_square {C : Type*} [Category C]
    {S S' T T' : C} (p : S ⟶ T) (p' : S' ⟶ T')
    [IsIso p] [IsIso p'] (a : S ⟶ S') (b : T ⟶ T')
    (h : p ≫ b = a ≫ p') : inv p ≫ a = b ≫ inv p' := by
  apply (cancel_mono p').1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

set_option linter.flexible false in
private theorem projection_naturality {P Q : derived d Y} (q : P ⟶ Q) :
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) q) ≫
        projection d f aY aX K Q =
      projection d f aY aX K P ≫
        (directImage d f).map
          (aX.tensor.map (Prod.mkHom (𝟙 K) ((pullback d f).map q))) := by
  exact (((proEtaleRingDerivedAdjunction f (ring d Y) (ring d X)
    (coefficients d f)).rightAdjointProjectionMap
    (T_C := Functor.curry.obj aX.tensor) (T_D := Functor.curry.obj aY.tensor)
    (Functor.curry.map (proEtaleCanonicalTensorComparison f (ring d Y) (ring d X)
      (coefficients d f) aY aX).hom ≫
        (Functor.curryObjProdComp (pullback d f) (pullback d f) aX.tensor).hom)).app K).naturality q

set_option linter.flexible false in
/-- Both the forward maps and their unique inverses commute with the whole quotient tower. -/
theorem tower_compatibility (n m : ℕ) (h : n ≤ m) :
    reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n ∧
    inverse d f aY aX K m ≫
      aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) =
    (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) ≫
      inverse d f aY aX K n := by
  have hnat := projection_naturality d f aY aX K (quotientMap d Y n m h)
  have hs := congrArg (fun z ↦ z ≫ (directImage d f).map
    (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))) hnat
  simp only [Category.assoc, ← Functor.map_comp, prod_comp,
    Category.comp_id] at hs
  rw [quotientDerivedPullback_naturality d f n m h] at hs
  have hf : reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n := by
    simpa only [reductionMap, Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id] using hs.symm
  refine ⟨hf, ?_⟩
  have := (reductionMap_isIso d f aY aX K m).2
  have := (reductionMap_isIso d f aY aX K n).2
  exact inverse_square _ _ _ _ hf

variable {n : ℕ} (r : Resolution d (X := X) (Y := Y) K n)

attribute [local irreducible] proEtaleOrdinaryTensorPullback

set_option linter.flexible false in
/-- The signed total chain mate, with differential d_I tensor 1 + (-1)^a 1 tensor d_F. -/
def Resolution.total :=
  SignedProjectionResolution.totalMate f (ring d Y) (ring d X) (coefficients d f)
    r.injective r.coefficient

set_option linter.flexible false in
/-- The normalized source comparison, specified by the mixed representative squares. -/
def Resolution.sourceModel :=
  SignedProjectionResolution.sourceModel f (ring d Y) (ring d X) (coefficients d f)
    aY K (quotient d Y n) r.injective r.isKInjective r.representsK
    r.coefficient r.representsQuotient r.package r.bounded

set_option linter.flexible false in
/-- The normalized target comparison, using exact pullback, mixed tensor and the
K-injective right-derived unit. -/
def Resolution.targetModel :=
  ((directImage d f).mapIso
    (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n)))).symm ≪≫
      SignedProjectionResolution.targetModel f (ring d Y) (ring d X) (coefficients d f)
        aX K (quotient d Y n) r.injective r.isKInjective r.representsK
        r.coefficient r.representsQuotient r.package r.bounded

section TotalizationProof

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingDerivedPullbackFactors

-- Avoid repeated inspection of the large representative tactic contexts.
end TotalizationProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem coefficientMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    coefficientMap d (f ≫ g) =
      (proEtaleRingInverseImageComp f g).hom.app (ring d Z) ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap d g) ≫
          coefficientMap d f := by
  apply limit.hom_ext
  intro n
  have hπ (V W : Scheme.{u}) (k : V ⟶ W) :
      coefficientMap d k ≫ limit.π (adicLisseRingSystem V d.ideal) n =
        (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem W d.ideal) n) ≫
            (proEtaleConstantComparison k).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1))) :=
    limit.lift_π _ n
  have : Finite (A ⧸ d.ideal ^ (n.unop + 1)) := d.quotientFinite n.unop
  let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
  have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n.unop
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ :=
    proEtale_profinite_coefficient_inverse_image Q
  have hc' := hc X Y Z f g n
  dsimp only [Q, proEtaleCoefficientTower, Functor.comp_obj,
    Functor.const_obj_obj] at hc'
  rw [hπ, hc']
  rw [← Category.assoc, ← Category.assoc]
  have hn := (proEtaleRingInverseImageComp f g).hom.naturality
    (limit.π (adicLisseRingSystem Z d.ideal) n)
  erw [hn]
  simp only [Functor.comp_map, Category.assoc]
  rw [hπ X Y f]
  conv_rhs => rw [← Functor.map_comp_assoc, hπ Y Z g, Functor.map_comp]
  simp only [Category.assoc]
  rfl

set_option linter.flexible false in
private theorem coefficients_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    proEtaleRingCompositeCoefficients f g (ring d Z) (ring d Y) (ring d X)
      (coefficients d g) (coefficients d f) = coefficients d (f ≫ g) := by
  apply Iso.ext
  unfold coefficients
  dsimp only [proEtaleRingCompositeCoefficients, asIso_hom]
  exact (coefficientMap_comp d f g).symm

-- The explicit intermediate objects preserve the native projection-square statement.
-- Keeping its functor compositions visible avoids evaluating derived functor objects.
section QuotientComposition

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors

end QuotientComposition

section BaseChange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)
  (aY' : ProEtaleTensorModel Y' (ring d Y'))
  (aX' : ProEtaleTensorModel X' (ring d X'))

set_option linter.flexible false in
/-- The canonical completed coefficient identifications agree around the square. -/
theorem coefficients_square (sq : ChosenCartesianSquare g' f' f g) : HEq
    (proEtaleRingCompositeCoefficients g' f (ring d Y) (ring d X) (ring d X')
      (coefficients d f) (coefficients d g'))
    (proEtaleRingCompositeCoefficients f' g (ring d Y) (ring d Y') (ring d X')
      (coefficients d g) (coefficients d f')) := by
  rw [coefficients_comp, coefficients_comp]
  have h := sq.w
  generalize g' ≫ f = k₁ at h ⊢
  generalize f' ≫ g = k₂ at h ⊢
  cases h
  rfl

set_option linter.flexible false in
/-- The actual base-change morphism, with the canonical completed coefficient coherence. -/
def exchange :=
  proEtaleAmbientRingedExchange sq (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq)

set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] proEtaleProjectionFormulaMate proEtaleAmbientRingedExchange
  proEtaleCanonicalTensorComparison

-- Avoid repeated inspection of the large native-operation tactic contexts.
end BaseChange

end AlgebraicGeometry.Scheme.PerfectProjection
