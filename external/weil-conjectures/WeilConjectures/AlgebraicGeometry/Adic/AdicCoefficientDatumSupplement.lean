/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum

/-!
# The completed coefficient ring and its strict derived reduction tower

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-adic-coefficient-datum, order 1239; Stacks Tags 06XN, 06YS, 06YY.
(blueprint: def-weil-pbc-adic-coefficient-datum).

The index n : ℕ denotes the positive exponent n+1. Every quotient reduction retains
its own coefficient action; tower levels restrict that action along the limit projection.
No constant/completed coefficient comparison is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.AdicCoefficients

private theorem ringHasWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) RingCat.{u + 1} := inferInstance

private theorem commRingHasWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) CommRingCat.{u + 1} := inferInstance

open scoped ChangeOfRings MonoidalCategory TensorProduct

/-- The nth quotient coefficient module with its completed scalar action.
Source: blueprint, Tags 06YY and 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def residue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (completedRing T I hf)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map
    (limit.π (ringSystem T I hf) (op n)))).obj
      (SheafOfModules.unit ((adicLisseForget T).obj ((ringSystem T I hf).obj (op n))))

end AlgebraicGeometry.Scheme.AdicCoefficients

namespace AlgebraicGeometry.Scheme

/-- Postcomposition by the actual quotient homomorphism, followed by sheafification.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionCoefficientMap (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    reductionCoefficient T d b ⟶ reductionCoefficient T d a :=
  (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map (homOfLE h).op

/-- Equal-index quotient coefficient maps are identities.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: quotient induction identifies the quotient map with the identity. Postcomposition
is then identity on component functions, and sheafification preserves identities. -/
theorem reductionCoefficientMap_id (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (a : ℕ) : reductionCoefficientMap T d a a (le_refl a) = 𝟙 _ := by
  exact (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map_id (op a)

/-- Quotient coefficient maps satisfy the quotient cocycle.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both quotient composites send the class of x to its class modulo I^(a+1).
Postcomposition and sheafification preserve that equality and composition. -/
theorem reductionCoefficientMap_comp (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionCoefficientMap T d c b hbc ≫ reductionCoefficientMap T d b a hab =
      reductionCoefficientMap T d c a (hab.trans hbc) := by
  exact ((AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map_comp
    (homOfLE hbc).op (homOfLE hab).op).symm

/-- Strict inverse sequences and compatible levelwise maps, indexed n↦n+1.
The coefficient ring B may be noncommutative.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev reductionTowerCategory (T : Scheme.{t}) (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :=
  ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B

/-- Strict module towers are Grothendieck abelian, including noncommutative coefficients.
Source: blueprint order 1239; Stacks Tags 079B and 079Q
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: replace the pro-etale site by its small skeleton in universe t+1. Apply
lem-weil-pbc-small-module-diagrams-grothendieck to the inverse-sequence index category.
Restriction along the site equivalence identifies the two module and diagram categories
and transports the Grothendieck structure. Kernels, cokernels, and exactness are
levelwise by lem-weil-tower-category-levelwise-abelian. -/
theorem reductionTower_isGrothendieckAbelian (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    IsGrothendieckAbelian.{t + 1} (reductionTowerCategory T B) := by
  let B' := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{t + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj B
  let : (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).functor.IsContinuous
      (ProEt.topology T) (proEtaleModelTopology T) := proEtaleModelUp_isContinuous T
  let : (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology T) (ProEt.topology T) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology T) (ProEt.topology T)
    infer_instance
  let e : SheafOfModules.{t + 1} B' ≌ SheafOfModules.{t + 1} B :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)) (𝟙 B) (𝟙 B')
      (by ext U; dsimp [AsSmall.equiv]; erw [B'.obj.map_id]; rfl)
      (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
  have : IsGrothendieckAbelian.{t + 1}
      (AsSmall.{t + 1} ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B') :=
    smallModuleDiagrams_isGrothendieckAbelian (proEtaleModelTopology T) B'
      (AsSmall.{t + 1} ℕᵒᵖ)
  let eJ : ℕᵒᵖ ≌ AsSmall.{t + 1} ℕᵒᵖ := AsSmall.equiv
  have : IsGrothendieckAbelian.{t + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B') :=
    IsGrothendieckAbelian.of_equivalence (Equivalence.congrLeft eJ.symm)
  exact IsGrothendieckAbelian.of_equivalence (Equivalence.congrRight e)

/-- Exact evaluation of a strict inverse sequence at the positive exponent n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionTowerEvaluation (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ (ringedSiteModules.{t + 1} B)).obj (op n)

/-- The standard derived category of completed-coefficient towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionTowerHasDerivedCategory (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    HasDerivedCategory (reductionTowerCategory T B) := HasDerivedCategory.standard _

/-- Derived evaluation is induced by the exact termwise evaluation functor.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionTowerDerivedEvaluation (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :=
  (reductionTowerEvaluation T B n).mapDerivedCategory

/-- The left-derived universal property determining scalar extension and its counit.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionDerivedUniversal (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionDerivedChange T φ).IsLeftDerivedFunctor (reductionDerivedCounit T φ)
      (HomotopyCategory.quasiIso (reductionModules T R) (ComplexShape.up ℤ)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.1

attribute [local instance] reductionModulesHasDerivedCategory

/-- Ordinary reduction, with the completion's action restored by restriction of scalars.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionLevel (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  reductionChange T (completedReductionProjection T d n) ⋙
    reductionRestrict T (completedReductionProjection T d n)

private theorem reductionChange_obj_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) :
    (reductionChange T φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
  (reductionChangeExistence T φ).choose_spec.choose M

private theorem reductionChange_map_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N) :
    (reductionChange T φ).map f = eqToHom (reductionChange_obj_eq T φ M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (reductionChange_obj_eq T φ N).symm :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose f

private theorem reductionChange_quasiIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules T R) ℤ} (f : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) (hf : QuasiIso f) :
    QuasiIso (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map f) :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.1
    f hP hQ hf

private theorem reductionDerivedCounit_isIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso ((reductionDerivedCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.2.2 P hP

attribute [local irreducible] reductionChange reductionDerivedChange

private theorem reductionTensor_map (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : reductionModules X R} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    ((reductionChange X φ).map a).val.app U
        (reductionTensorSection X φ M U s x) =
      reductionTensorSection X φ N U s (a.val.app U x) := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let h : ∀ M : reductionModules X R, (reductionChange X φ).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
    (reductionChange_obj_eq X φ)
  have ha := reductionChange_map_eq X φ a
  change (reductionChange X φ).map a = _ at ha
  let b : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (a.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u + 1, u + 1} φ M a }
  let adjS := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (reductionModuleRing X S).obj)
  have hn := congrArg (fun t ↦ t.app U
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
      (adjS.unit.naturality b)
  have hc : eqToHom (h M).symm ≫ (reductionChange X φ).map a =
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M a ≫ eqToHom (h N).symm := by
    rw [ha]
    simp
  have hc' := congrArg (fun t : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶
      (reductionChange X φ).obj N ↦ t.val.app U
        ((toSheafify (ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) hc
  change _ = _ at hn
  change _ = _ at hc'
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hc'
  with_unfolding_all
    exact hc'.trans (congrArg ((eqToHom (h N).symm).val.app U) hn.symm)

private theorem reductionTensor_hom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : Sheaf (ProEt.topology T) AddCommGrpCat.{t + 1})
    (f g : (SheafOfModules.toSheaf (reductionModuleRing T S)).obj
      ((reductionChange T φ).obj M) ⟶ N)
    (h : ∀ V s x, f.hom.app V (reductionTensorSection T φ M V s x) =
      g.hom.app V (reductionTensorSection T φ M V s x)) : f = g := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let e := eqToHom ((reductionChange_obj_eq T φ) M).symm
  apply (cancel_epi ((SheafOfModules.toSheaf (reductionModuleRing T S)).map e)).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology T) _ _ N.property
  ext V z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s x => with_unfolding_all exact h V s x

private theorem ordinaryAdjunction_exists (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    ∃ a : reductionChange X φ ⊣ reductionRestrict X φ,
      ∀ (M : reductionModules X R) (N : reductionModules X S)
        (f : (reductionChange X φ).obj M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        HEq ((a.homEquiv M N f).val.app U x)
          (f.val.app U (reductionTensorSection X φ M U 1 x)) := by
  let h := reductionChange_obj_eq X φ
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (J := ProEt.topology X) φ
  obtain ⟨a, ha⟩ := ho (reductionChange X φ) h (reductionChange_map_eq X φ)
  refine ⟨a, ?_⟩
  intro M N f U x
  have hh := ha M N (eqToHom (h M).symm ≫ f) U x
  have hi : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hi] at hh
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  with_unfolding_all exact heq_of_eq hh

private def reductionUnit (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) :
    M ⟶ (reductionRestrict X φ).obj ((reductionChange X φ).obj M) := by
  have h := (ordinaryAdjunction_exists X φ).choose.unit.app M
  exact h

private theorem reductionUnit_apply (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (reductionUnit X φ M).val.app U x = reductionTensorSection X φ M U 1 x := by
  have hh := (ordinaryAdjunction_exists X φ).choose_spec M
    ((reductionChange X φ).obj M) (𝟙 _) U x
  let adj := (ordinaryAdjunction_exists X φ).choose
  have hi : adj.homEquiv M ((reductionChange X φ).obj M) (𝟙 _) = adj.unit.app M := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hv := congrArg (fun f : M ⟶ (reductionRestrict X φ).obj
    ((reductionChange X φ).obj M) ↦ f.val.app U x) hi
  exact hv.symm.trans (eq_of_heq hh)

private theorem level_hom_ext (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : reductionModules X R)
    (f g : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (reductionTensorSection X φ M U s x) =
        g.val.app U (reductionTensorSection X φ M U s x)) : f = g := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let hM := (reductionChange_obj_eq X φ) M
  apply (SheafOfModules.toSheaf (reductionModuleRing X R)).map_injective
  let adjS := sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}
  let j := (SheafOfModules.toSheaf _).map (eqToHom hM.symm)
  apply (cancel_epi j).mp
  apply (adjS.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s x => with_unfolding_all exact h U s x

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorSection_smul (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : reductionModules X R)
    (U : X.ProEtᵒᵖ) (s t : S.obj.obj U)
    (x : M.val.obj U) :
    s • reductionTensorSection X φ M U t x =
      reductionTensorSection X φ M U (s * t) x := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let b : T ⟶ ((reductionChange X φ).obj M).val :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (reductionModuleRing X S).obj)).unit.app T ≫
      (eqToHom ((reductionChange_obj_eq X φ) M).symm).val
  with_unfolding_all change s • b.app U (t ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = _
  rw [← map_smul]
  with_unfolding_all rfl

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem step_map_exists (X : Scheme.{u})
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (q : S ⟶ T) (hcomp : φ ≫ q = ψ)
    (M : reductionModules X R) (unitMap : M ⟶ (reductionRestrict X ψ).obj
      ((reductionChange X ψ).obj M))
    (hunit : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      unitMap.val.app U x = reductionTensorSection X ψ M U 1 x) :
    ∃ b : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
        (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M),
      ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        b.val.app U (reductionTensorSection X φ M U s x) =
          reductionTensorSection X ψ M U (q.hom.app U s) x := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let N := (reductionRestrict X q).obj ((reductionChange X ψ).obj M)
  have hq (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
      q.hom.app U (φ.hom.app U r) = ψ.hom.app U r :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hcomp) r
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing X R).obj).map unitMap.val
  let a : M ⟶ (reductionRestrict X φ).obj N :=
    ⟨PresheafOfModules.homMk ua (by
        intro U r x
        have h := (unitMap.val.app U).hom.map_smul r x
        change unitMap.val.app U (r • x) =
          q.hom.app U (φ.hom.app U r) •
            (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x)
        rw [hq]
        exact h)⟩
  let adj := (ordinaryAdjunction_exists X φ).choose
  let b : (reductionChange X φ).obj M ⟶ N := (adj.homEquiv M N).symm a
  let ub := (PresheafOfModules.toPresheaf (reductionModuleRing X S).obj).map b.val
  let c : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
      (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M) :=
    ⟨PresheafOfModules.homMk ub (by
        intro U r x
        have h := (b.val.app U).hom.map_smul (φ.hom.app U r) x
        change b.val.app U ((φ.hom.app U r) •
            (show ((reductionChange X φ).obj M).val.obj U from x)) =
          ψ.hom.app U r •
            (show ((reductionChange X ψ).obj M).val.obj U from b.val.app U x)
        rw [← hq]
        exact h)⟩
  refine ⟨c, ?_⟩
  intro U s x
  change b.val.app U (reductionTensorSection X φ M U s x) = _
  have hb : b.val.app U (reductionTensorSection X φ M U 1 x) = a.val.app U x := by
    have hh := (ordinaryAdjunction_exists X φ).choose_spec M N b U x
    rw [Equiv.apply_symm_apply] at hh
    exact (eq_of_heq hh).symm
  have ht := tensorSection_smul X φ M U s 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hb]
  change q.hom.app U s •
    (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x) = _
  rw [hunit, tensorSection_smul, mul_one]

private theorem scalarTransition_exists (X : Scheme.{u})
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (q : S ⟶ T) (hcomp : φ ≫ q = ψ) :
    ∃! τ : reductionChange X φ ⋙ reductionRestrict X φ ⟶
        reductionChange X ψ ⋙ reductionRestrict X ψ,
      ∀ (M : reductionModules X R) (U : X.ProEtᵒᵖ)
        (s : S.obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection X φ M U s x) =
          reductionTensorSection X ψ M U (q.hom.app U s) x := by
  let f (M : reductionModules X R) :=
    (step_map_exists X φ ψ q hcomp M (reductionUnit X ψ M)
      (reductionUnit_apply X ψ M)).choose
  have hf (M : reductionModules X R) :=
    (step_map_exists X φ ψ q hcomp M (reductionUnit X ψ M)
      (reductionUnit_apply X ψ M)).choose_spec
  let τ : reductionChange X φ ⋙ reductionRestrict X φ ⟶
      reductionChange X ψ ⋙ reductionRestrict X ψ :=
    { app := f
      naturality := by
        intro M N k
        apply level_hom_ext X φ M ((reductionRestrict X ψ).obj
          ((reductionChange X ψ).obj N))
        intro V s x
        change (f N).val.app V (((reductionChange X φ).map k).val.app V
            (reductionTensorSection X φ M V s x)) =
          ((reductionChange X ψ).map k).val.app V ((f M).val.app V
            (reductionTensorSection X φ M V s x))
        rw [reductionTensor_map, hf, hf, reductionTensor_map] }
  refine ⟨τ, ?_, ?_⟩
  · intro M V s x
    exact hf M V s x
  · intro τ' hτ'
    apply NatTrans.ext
    funext M
    apply level_hom_ext X φ M ((reductionRestrict X ψ).obj
      ((reductionChange X ψ).obj M))
    intro V s x
    exact (hτ' M V s x).trans (hf M V s x).symm

/-- The unique natural transition sending s⊗x to q(s)⊗x after scalar restriction.
Source: blueprint order 1239, Stacks Tag 03EK
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the limit relation π_a=q_(b,a)π_b makes the displayed tensor formula balanced.
Extend on presheaf tensors and sheafify. It is linear over the completion, commutes with
restrictions, and is natural in M. Local pure tensors generate the sheafification, giving
uniqueness of the natural transformation. -/
theorem completedReductionTransition_exists (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    ∃! τ : completedReductionLevel T d b ⟶ completedReductionLevel T d a,
      ∀ (M : reductionModules T (completedReductionCoefficient T d)) (U : T.ProEtᵒᵖ)
        (s : (reductionCoefficient T d b).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection T
          (completedReductionProjection T d b) M U s x) =
          reductionTensorSection T (completedReductionProjection T d a) M U
            ((reductionCoefficientMap T d b a h).hom.app U s) x := by
  exact scalarTransition_exists T (completedReductionProjection T d b)
    (completedReductionProjection T d a) (reductionCoefficientMap T d b a h)
    (limit.w (reductionCoefficientSystem T d) (homOfLE h).op)

/-- The canonical transition, specified uniquely on tensor generators.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTransition (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    completedReductionLevel T d b ⟶ completedReductionLevel T d a :=
  (completedReductionTransition_exists T d b a h).exists.choose

/-- The ordinary strict tower of a module sheaf, at all positive powers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionModuleTower (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : reductionModules T (completedReductionCoefficient T d)) :=
  Functor.ofOpSequence (X := fun n ↦ (completedReductionLevel T d n).obj M)
    (fun n ↦ (completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M)

/-- Naturality at consecutive indices supplies a compatible levelwise map of towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the transitions are natural transformations; their naturality square is exactly
this equality. Functor.ofOpSequence has the stipulated consecutive transition. -/
theorem completedReductionTowerMap_naturality (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {M N : reductionModules T (completedReductionCoefficient T d)} (f : M ⟶ N)
    (n : ℕ) :
    (completedReductionModuleTower T d M).map (homOfLE (Nat.le_succ n)).op ≫
        (completedReductionLevel T d n).map f =
      (completedReductionLevel T d (n + 1)).map f ≫
        (completedReductionModuleTower T d N).map (homOfLE (Nat.le_succ n)).op := by
  simpa only [completedReductionModuleTower, Functor.ofOpSequence_map_homOfLE_succ] using
    ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).naturality f).symm

/-- The ordinary tower construction on module morphisms.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionModuleTowerFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    reductionModules T (completedReductionCoefficient T d) ⥤
      reductionTowerCategory T (reductionModuleRing T (completedReductionCoefficient T d)) where
  obj M := completedReductionModuleTower T d M
  map f := NatTrans.ofOpSequence (fun n ↦ (completedReductionLevel T d n).map f)
    (completedReductionTowerMap_naturality T d f)
  map_id M := NatTrans.ext (funext (fun n ↦ (completedReductionLevel T d n.unop).map_id M))
  map_comp f g := NatTrans.ext (funext (fun n ↦ (completedReductionLevel T d n.unop).map_comp f g))

/-- The module-to-tower tensor construction is additive, levelwise.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: scalar extension and scalar restriction are additive. Equality of tower morphisms
is equality of their components, so their composite level functors prove additivity. -/
@[instance]
theorem completedReductionModuleTowerFunctor_additive (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor T d).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  have : (completedReductionLevel T d n.unop).Additive := by
    unfold completedReductionLevel reductionRestrict
    infer_instance
  exact (completedReductionLevel T d n.unop).map_add (f := f) (g := g)

/-- Apply the additive tower construction to terms and differentials. This gives actual
complexes in the tower category, not merely towers of derived objects.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionComplexTowerFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :=
  (completedReductionModuleTowerFunctor T d).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact functor from the homotopy category to the derived category of towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionHomotopyFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :=
  (completedReductionModuleTowerFunctor T d).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The universal property and representative computation of a reduction-tower pair.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def IsCompletedReductionTowerPair (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (LF : reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
      DerivedCategory (reductionTowerCategory T
        (reductionModuleRing T (completedReductionCoefficient T d))))
    (ε : DerivedCategory.Qh ⋙ LF ⟶ completedReductionHomotopyFunctor T d) : Prop :=
  LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (reductionModules T (completedReductionCoefficient T d))
        (ComplexShape.up ℤ)) ∧
    (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
    ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
        (R := completedReductionCoefficient T d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))

universe uB vB wB uD vD wD

private theorem mapComplex_comp_eq
    {B D H : Type*} [Category B] [Category D] [Category H]
    [Preadditive B] [Preadditive D] [Preadditive H]
    (F : B ⥤ D) [F.Additive] (G : D ⥤ H) [G.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) =
      (F ⋙ G).mapHomologicalComplex (.up ℤ) := by rfl

private theorem mapComplex_eq_of_eq
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    (F G : B ⥤ D) [F.Additive] [G.Additive] (h : F = G) :
    F.mapHomologicalComplex (.up ℤ) = G.mapHomologicalComplex (.up ℤ) := by
  subst G
  rfl

private theorem level_module_eq (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionModuleTowerFunctor T d ⋙
        reductionTowerEvaluation T (reductionModuleRing T (completedReductionCoefficient T d)) n =
      reductionChange T (completedReductionProjection T d n) ⋙
        reductionRestrict T (completedReductionProjection T d n) := by rfl

private theorem level_complex_eq (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionComplexTowerFunctor T d ⋙
        (reductionTowerEvaluation T
          (reductionModuleRing T (completedReductionCoefficient T d)) n).mapHomologicalComplex
          (.up ℤ) =
      (reductionChange T (completedReductionProjection T d n)).mapHomologicalComplex (.up ℤ) ⋙
        (reductionRestrict T (completedReductionProjection T d n)).mapHomologicalComplex
          (.up ℤ) := by
  exact (mapComplex_comp_eq _ _).trans
    ((mapComplex_eq_of_eq _ _ (level_module_eq T d n)).trans
      (mapComplex_comp_eq _ _).symm)

attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionModuleTowerFunctor
attribute [local irreducible] completedReductionCoefficient
attribute [local irreducible] reductionCoefficientSystem AdicCoefficients.ringSystem

private theorem quasiIso_composite_map
    {B D H : Type*} [Category B] [Category D] [Category H]
    [Abelian B] [Abelian D] [Abelian H]
    (F : B ⥤ D) [F.Additive] (G : D ⥤ H) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {P Q : CochainComplex B ℤ} (a : P ⟶ Q)
    (ha : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map a)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)).map a) := by
  let := ha
  change QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map a))
  infer_instance

private theorem quasiIso_map_of_functor_eq
    {B D : Type*} [Category B] [Category D] [Abelian B] [Abelian D]
    (F G : CochainComplex B ℤ ⥤ CochainComplex D ℤ) (h : F = G)
    {P Q : CochainComplex B ℤ} (a : P ⟶ Q) (ha : QuasiIso (G.map a)) :
    QuasiIso (F.map a) := by
  subst G
  exact ha

private theorem derivedPair_from_complex_resolutions
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (E : B ⥤ D) [E.Additive] (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ,
      ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S P ∧ QuasiIso p)
    (hinv : ∀ {P Q : CochainComplex B ℤ} (a : P ⟶ Q), S P → S Q → QuasiIso a →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map a)) :
    ∃ (LF : DerivedCategory B ⥤ DerivedCategory D)
      (ε : DerivedCategory.Qh ⋙ LF ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex B ℤ, S P →
          IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)) := by
  let H := HomotopyCategory.quotient B (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S' : Set (HomotopyCategory B (.up ℤ)) := {X | ∃ P, S P ∧ H.obj P = X}
  have hr (X : HomotopyCategory B (.up ℤ)) :
      ∃ (X' : HomotopyCategory B (.up ℤ)) (a : X' ⟶ X),
        X' ∈ S' ∧ HomotopyCategory.quasiIso B (.up ℤ) a := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, p, hP, hp⟩ := hres X
    exact ⟨H.obj P, H.map p, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hi (X Y : HomotopyCategory B (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ S') (hY : Y ∈ S') (hs : HomotopyCategory.quasiIso B (.up ℤ) s) :
      IsIso (F.map s) := by
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨Q, hQ, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := H.map_surjective s
    have ha := hinv a hP hQ ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs)
    dsimp only [F, Functor.comp_map, H]
    rw [Functor.mapHomotopyCategory_map]
    with_unfolding_all
      exact Localization.inverts
        (DerivedCategory.Qh : HomotopyCategory D (.up ℤ) ⥤ DerivedCategory D)
        (HomotopyCategory.quasiIso D (.up ℤ))
        _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ha)
  obtain ⟨_, LF, ε, hLF, htri, hcompute⟩ :=
    Functor.leftDerived_from_resolvingClass B (DerivedCategory D) F S' hr hi
  exact ⟨LF, ε, hLF, htri, fun P hP ↦ hcompute (H.obj P) ⟨P, hP, rfl⟩⟩

/-- The reduction tower has its universal left derived pair, computed on every K-flat
complex; in particular the construction is functorial only after derived localization.
Source: blueprint order 1239; Stacks Tags 06XN, 06YS, 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the additive termwise tower construction preserves shifts and mapping cones.
Every representative has a K-flat resolution by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings it sends quasi-isomorphisms between K-flat complexes to
levelwise quasi-isomorphisms. Tower cohomology is levelwise, hence these are tower
quasi-isomorphisms. Apply lem-pur-left-derived-from-kflat-class to obtain the universal
pair, its exactness and its counit isomorphisms at K-flat representatives. -/
theorem completedReductionTower_exists (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    ∃ (LF : reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
        DerivedCategory (reductionTowerCategory T
          (reductionModuleRing T (completedReductionCoefficient T d))))
      (ε : DerivedCategory.Qh ⋙ LF ⟶ completedReductionHomotopyFunctor T d),
      IsCompletedReductionTowerPair T d LF ε := by
  unfold IsCompletedReductionTowerPair completedReductionHomotopyFunctor
  apply derivedPair_from_complex_resolutions (completedReductionModuleTowerFunctor T d)
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P)
  · intro X
    obtain ⟨P, p, hk, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) X
    exact ⟨P, p, hk, hp⟩
  · intro P Q a hP hQ ha
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    apply quasiIso_map_of_functor_eq _ _ (level_complex_eq T d n.unop) a
    exact quasiIso_composite_map
      (reductionChange T (completedReductionProjection T d n.unop))
      (reductionRestrict T (completedReductionProjection T d n.unop)) a
      (reductionChange_quasiIso T (completedReductionProjection T d n.unop) a hP hQ ha)

/-- K↦K_bullet is the canonical left derived functor, with its universal comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTower (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
      DerivedCategory (reductionTowerCategory T
        (reductionModuleRing T (completedReductionCoefficient T d))) :=
  (completedReductionTower_exists T d).choose

/-- The ordinary coefficient-change complex, with its actual scalar-extension differential.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionChangeComplex (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    CochainComplex (reductionModules T R) ℤ ⥤ CochainComplex (reductionModules T S) ℤ :=
  (reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical balancing chain map is uniquely determined on local tensor generators.
Source: blueprint order 1239, normalization paragraph; Stacks Tag 03EK
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: send s tensor (r tensor x) to (s*ψ(r)) tensor x. The relation ψφ=χ makes
this balanced over both rings. Sheafification extends it uniquely; restrictions and
differentials commute with the formula. The inverse sends s tensor x to s tensor
(1 tensor x). Balancing verifies both inverse identities. Local tensor generation
proves uniqueness, including on the empty site object. -/
theorem reductionBalance_exists (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    ∃! f : (reductionChangeComplex T ψ).obj ((reductionChangeComplex T φ).obj P) ⟶
        (reductionChangeComplex T χ).obj P,
      IsIso f ∧ ∀ (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
        (x : (P.X p).val.obj V),
        (f.f p).val.app V
          (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
            (reductionTensorSection T φ (P.X p) V r x)) =
          reductionTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x := by
  unfold reductionChangeComplex reductionChange reductionTensorSection
  exact completedAdicBalance_exists T φ ψ χ _h P

/-- The canonical balancing map, selected from its unique local tensor formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionBalance (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T ψ).obj ((reductionChangeComplex T φ).obj P) ⟶
      (reductionChangeComplex T χ).obj P :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose

/-- The balancing map is invertible, by its defining characterization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionBalance_isIso (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) : IsIso (reductionBalance T φ ψ χ h P) :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose_spec.1

/-- The completion projection followed by a quotient transition is the earlier projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: this is the limit cone's naturality equation for the arrow b to a in the
strict quotient coefficient system. -/
theorem completedReductionProjection_comp (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    completedReductionProjection T d b ≫ reductionCoefficientMap T d b a h =
      completedReductionProjection T d a := by
  with_unfolding_all exact limit.w (reductionCoefficientSystem T d) (homOfLE h).op

private theorem reductionBalance_tmul (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ)
    (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
    (x : (P.X p).val.obj V) :
    ((reductionBalance T φ ψ χ h P).f p).val.app V
      (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
        (reductionTensorSection T φ (P.X p) V r x)) =
      reductionTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose_spec.2 p V s r x

private theorem reductionBalance_hom_ext (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ)
    {Q : CochainComplex (reductionModules T U) ℤ}
    (f g : (reductionChangeComplex T ψ).obj ((reductionChangeComplex T φ).obj P) ⟶ Q)
    (hf : ∀ p V s r x, (f.f p).val.app V
        (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
          (reductionTensorSection T φ (P.X p) V r x)) =
      (g.f p).val.app V (reductionTensorSection T ψ
        ((reductionChange T φ).obj (P.X p)) V s
          (reductionTensorSection T φ (P.X p) V r x))) : f = g := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let β := reductionBalance T φ ψ χ h P
  apply (cancel_epi (inv β)).1
  apply HomologicalComplex.Hom.ext
  funext p
  apply (SheafOfModules.toSheaf (reductionModuleRing T U)).map_injective
  apply reductionTensor_hom_ext T χ (P.X p)
  intro V s x
  have hb := reductionBalance_tmul T φ ψ χ h P p V s 1 x
  simp only [map_one, mul_one] at hb
  have hc := congrArg (fun k ↦ (k.f p).val.app V
    (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
      (reductionTensorSection T φ (P.X p) V 1 x))) (IsIso.hom_inv_id β)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hc
  change ((inv β).f p).val.app V
    (((reductionBalance T φ ψ χ h P).f p).val.app V _) = _ at hc
  rw [hb] at hc
  change (f.f p).val.app V (((inv β).f p).val.app V _) =
    (g.f p).val.app V (((inv β).f p).val.app V _)
  rw [hc]
  exact hf p V s 1 x

/-- Balancing is natural on all representatives and therefore on K-flat computations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both composites send s tensor (r tensor x) to (s*ψ(r)) tensor f(x).
Local tensor generators give equality in each degree, and localization preserves it. -/
theorem reductionBalance_naturality (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    {P Q : CochainComplex (reductionModules T R) ℤ} (f : P ⟶ Q) :
    (reductionChangeComplex T ψ).map ((reductionChangeComplex T φ).map f) ≫
        reductionBalance T φ ψ χ h Q =
      reductionBalance T φ ψ χ h P ≫ (reductionChangeComplex T χ).map f := by
  apply reductionBalance_hom_ext T φ ψ χ h P
  intro p V s r x
  change ((reductionBalance T φ ψ χ h Q).f p).val.app V
      (((reductionChange T ψ).map ((reductionChange T φ).map (f.f p))).val.app V
        (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
          (reductionTensorSection T φ (P.X p) V r x))) =
    ((reductionChange T χ).map (f.f p)).val.app V
      (((reductionBalance T φ ψ χ h P).f p).val.app V
        (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
          (reductionTensorSection T φ (P.X p) V r x)))
  rw [reductionTensor_map, reductionTensor_map, reductionBalance_tmul,
    reductionBalance_tmul, reductionTensor_map]

/-- The consecutive transition is natural in strict towers.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the naturality square of a tower morphism at n+1 to n is the stated equation. -/
theorem completedTowerEvaluationStep_naturality (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ)
    {M N : reductionTowerCategory T B} (f : M ⟶ N) :
    f.app (op (n + 1)) ≫ N.map (homOfLE (Nat.le_succ n)).op =
      M.map (homOfLE (Nat.le_succ n)).op ≫ f.app (op n) := by
  exact (f.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The natural transformation between consecutive exact evaluation functors.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedTowerEvaluationStep (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :
    reductionTowerEvaluation T B (n + 1) ⟶ reductionTowerEvaluation T B n where
  app M := M.map (homOfLE (Nat.le_succ n)).op
  naturality _ _ f := completedTowerEvaluationStep_naturality T B n f

/-- The evaluated derived objects, including arbitrary derived strict towers.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedTowerDerivedSequence (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d)))) (n : ℕ) :=
  (reductionTowerDerivedEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) n).obj M

/-- Derived transitions are the termwise transitions of exact evaluation, localized.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedTowerDerivedStep (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d)))) (n : ℕ) :
    completedTowerDerivedSequence T d M (n + 1) ⟶ completedTowerDerivedSequence T d M n :=
  (Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _
    (reductionTowerDerivedEvaluation T
      (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1))
    (reductionTowerDerivedEvaluation T
      (reductionModuleRing T (completedReductionCoefficient T d)) n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
      (reductionModuleRing T (completedReductionCoefficient T d)) n) (ComplexShape.up ℤ))
        DerivedCategory.Q)).app M

end AlgebraicGeometry.Scheme

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
namespace AlgebraicGeometry.Scheme

attribute [local instance] reductionModulesHasDerivedCategory

attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionModuleTowerFunctor
attribute [local irreducible] completedReductionCoefficient
attribute [local irreducible] reductionCoefficientSystem AdicCoefficients.ringSystem

/-- Read a universal homotopy counit on a complex using the canonical factorization maps.
Source: Stacks Tags 06XN and 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionComplexCounit
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  L.map ((DerivedCategory.quotientCompQhIso B).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- The canonical scalar-extension comparison on any complex representative.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionScalarComplexCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ) :=
  reductionComplexCounit (reductionChange T φ) (reductionDerivedChange T φ)
    (reductionDerivedCounit T φ) P

/-- The exact derived coefficient restriction, applied termwise before localization.
Source: blueprint order 1239; Stacks Tag 015F
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionDerivedRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (reductionRestrict T φ).mapDerivedCategory

universe v w u' v' w'
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true

private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂])

private theorem kan_precomp_quotient
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (q : A ⥤ B) [((whiskeringLeft A B H).obj q).Full]
    [((whiskeringLeft A B H).obj q).Faithful]
    (L : B ⥤ D) (G : B ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G) [F.IsRightKanExtension α] :
    F.IsRightKanExtension ((Functor.associator q L F).hom ≫ whiskerLeft q α) := by
  let P := RightExtension.precomp L G q
  have : P.IsEquivalence := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let β := (Functor.associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  exact ⟨⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) e⟩⟩

private noncomputable def complexCounitNat
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  let q := HomotopyCategory.quotient B (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  whiskerRight (DerivedCategory.quotientCompQhIso B).inv L ≫
    (Functor.associator q DerivedCategory.Qh L).hom ≫ whiskerLeft q ε ≫ j.hom

private theorem complexCounitNat_app
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) (P : CochainComplex B ℤ) :
    (complexCounitNat E L ε).app P = reductionComplexCounit E L ε P := by
  simp [complexCounitNat, reductionComplexCounit]

private theorem complexCounitNat_kan
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] :
    L.IsLeftDerivedFunctor (complexCounitNat E L ε)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
  have : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso B (.up ℤ))
  have := kan_precomp_quotient (HomotopyCategory.quotient B (.up ℤ))
    DerivedCategory.Qh
    (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) L ε
  let q := HomotopyCategory.quotient B (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let α := (Functor.associator q DerivedCategory.Qh L).hom ≫ whiskerLeft q ε
  have hh := kan_change_iso L (DerivedCategory.quotientCompQhIso B) j α
  constructor
  simpa only [complexCounitNat, α, j, Category.assoc] using hh

private theorem derived_natTrans_ext
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α β : F ⟶ G) (h : ∀ P, S P → α.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
  obtain ⟨P, p, hP, hp⟩ := hres K
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
  let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, β.naturality, h P hP]

private theorem derived_natTrans_isIso
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α : F ⟶ G) (h : ∀ P, S P → IsIso (α.app (DerivedCategory.Q.obj P))) :
    IsIso α := by
  have hi (X : DerivedCategory B) : IsIso (α.app X) := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
    obtain ⟨P, p, hP, hp⟩ := hres K
    have : IsIso (DerivedCategory.Q.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
    have := h P hP
    let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
    have eq : α.app X = inv (F.map i.hom) ≫ α.app (DerivedCategory.Q.obj P) ≫
        G.map i.hom := by
      rw [← α.naturality, IsIso.inv_hom_id_assoc]
    rw [eq]
    infer_instance
  exact NatIso.isIso_of_isIso_app α

private def reductionRawComplexIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T φ).obj P ≅ SheafOfModules.changeOfRingsComplex.{t + 1, t} φ P := by
  let h : ∀ M : reductionModules T R, (reductionChange T φ).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
    reductionChange_obj_eq T φ
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦ eqToIso (h (P.X p))) ?_
  intro p q hpq
  have hd := reductionChange_map_eq T φ (P.d p q)
  change (reductionChange T φ).map (P.d p q) = _ at hd
  change eqToHom (h (P.X p)) ≫
      SheafOfModules.changeOfRingsHom φ (P.X p) (P.d p q) =
    (reductionChange T φ).map (P.d p q) ≫ eqToHom (h (P.X q))
  rw [hd]
  simp

private theorem reductionChange_isKFlat (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((reductionChangeComplex T φ).obj P) := by
  let _ := SheafOfModules.monoidalCategory S
  have hflat' (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)) := by
    exact hflat i
  have hk := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{t + 1, t} φ P hP hflat').1
  intro F hF i
  have e := (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ)
    (.up ℤ)).obj F).mapIso (reductionRawComplexIso T φ P)
  exact (hk F hF i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ)).symm

private theorem scalarCounit_isIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (reductionScalarComplexCounit T φ P) := by
  have : IsIso ((reductionDerivedCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    reductionDerivedCounit_isIso T φ P hP
  dsimp only [reductionScalarComplexCounit, reductionComplexCounit]
  infer_instance

private def balanceNat (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ) :
    reductionChangeComplex T φ ⋙ reductionChangeComplex T ψ ⟶ reductionChangeComplex T χ where
  app P := reductionBalance T φ ψ χ h P
  naturality _ _ f := reductionBalance_naturality T φ ψ χ h f

private theorem derivedReductionComposition (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ) :
    ∃! τ : reductionDerivedChange T φ ⋙ reductionDerivedChange T ψ ⟶ reductionDerivedChange T χ,
      IsIso τ ∧ ∀ P : CochainComplex (reductionModules T R) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        τ.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T χ P =
          (reductionDerivedChange T ψ).map (reductionScalarComplexCounit T φ P) ≫
          reductionScalarComplexCounit T ψ ((reductionChangeComplex T φ).obj P) ≫
          DerivedCategory.Q.map (reductionBalance T φ ψ χ h P) := by
  let eφ := complexCounitNat (reductionChange T φ) (reductionDerivedChange T φ)
    (reductionDerivedCounit T φ)
  let eψ := complexCounitNat (reductionChange T ψ) (reductionDerivedChange T ψ)
    (reductionDerivedCounit T ψ)
  let eχ := complexCounitNat (reductionChange T χ) (reductionDerivedChange T χ)
    (reductionDerivedCounit T χ)
  have := complexCounitNat_kan (reductionChange T χ) (reductionDerivedChange T χ)
    (reductionDerivedCounit T χ)
  let L := reductionDerivedChange T φ ⋙ reductionDerivedChange T ψ
  let β : DerivedCategory.Q ⋙ L ⟶ reductionChangeComplex T χ ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ whiskerRight eφ (reductionDerivedChange T ψ) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft (reductionChangeComplex T φ) eψ ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight (balanceNat T φ ψ χ h) DerivedCategory.Q
  let τ := (reductionDerivedChange T χ).leftDerivedLift eχ
    (HomologicalComplex.quasiIso (reductionModules T R) (.up ℤ)) L β
  have ht (P : CochainComplex (reductionModules T R) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T χ P =
        (reductionDerivedChange T ψ).map (reductionScalarComplexCounit T φ P) ≫
        reductionScalarComplexCounit T ψ ((reductionChangeComplex T φ).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T φ ψ χ h P) := by
    have hf := (reductionDerivedChange T χ).leftDerived_fac_app eχ
      (HomologicalComplex.quasiIso (reductionModules T R) (.up ℤ)) L β P
    change τ.app (DerivedCategory.Q.obj P) ≫ eχ.app P = β.app P at hf
    have hb : β.app P =
        (reductionDerivedChange T ψ).map (reductionScalarComplexCounit T φ P) ≫
        reductionScalarComplexCounit T ψ ((reductionChangeComplex T φ).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T φ ψ χ h P) := by
      change (𝟙 _ ≫ (reductionDerivedChange T ψ).map (eφ.app P) ≫
        𝟙 _ ≫ eψ.app ((reductionChangeComplex T φ).obj P) ≫
        𝟙 _ ≫ DerivedCategory.Q.map (reductionBalance T φ ψ χ h P)) = _
      simp only [Category.id_comp, eφ, eψ, complexCounitNat_app]
    have hc : eχ.app P = reductionScalarComplexCounit T χ P :=
      complexCounitNat_app _ _ _ _
    rw [hc] at hf
    exact hf.trans hb
  let S₀ (P : CochainComplex (reductionModules T R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i))
  have hres (X : CochainComplex (reductionModules T R) ℤ) :
      ∃ (P : CochainComplex (reductionModules T R) ℤ) (p : P ⟶ X), S₀ P ∧ QuasiIso p := by
    obtain ⟨P, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨P, p, ⟨hk, hf⟩, hp⟩
  refine ⟨τ, ⟨?_, fun P _ ↦ ht P⟩, ?_⟩
  · apply derived_natTrans_isIso L (reductionDerivedChange T χ) S₀ hres τ
    intro P hP
    have := scalarCounit_isIso T φ P hP.1
    have := scalarCounit_isIso T χ P hP.1
    have := scalarCounit_isIso T ψ ((reductionChangeComplex T φ).obj P)
      (reductionChange_isKFlat T φ P hP.1 hP.2)
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T χ P) := by
      rw [ht P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (reductionScalarComplexCounit T χ P)
  · intro τ' hτ'
    apply derived_natTrans_ext L (reductionDerivedChange T χ) S₀ hres
    intro P hP
    have := scalarCounit_isIso T χ P hP.1
    apply (cancel_mono (reductionScalarComplexCounit T χ P)).1
    exact (hτ'.2 P hP.1).trans (ht P).symm

/-- The quotient normalization is uniquely specified on every K-flat computation by
ordinary balancing and the universal scalar-extension counits.
Source: blueprint order 1239, normalization paragraph; Stacks Tag 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: scalar extension carries K-flat complexes to K-flat complexes, by testing against
acyclic target complexes and restricting scalars. On those representatives the two
successive derived changes are computed by successive ordinary changes. Balancing gives
an isomorphism to direct scalar extension. The local tensor formula proves naturality,
so these maps descend through quasi-isomorphisms between K-flat complexes. Every object
has such a representative. The universal counits give the displayed characterization
and show uniqueness, since their components are invertible on those representatives. -/
theorem completedReductionDerivedNormalization_exists (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    ∃! τ : reductionDerivedChange T (completedReductionProjection T d b) ⋙
        reductionDerivedChange T (reductionCoefficientMap T d b a h) ⟶
          reductionDerivedChange T (completedReductionProjection T d a),
      IsIso τ ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            reductionScalarComplexCounit T (completedReductionProjection T d a) P =
          (reductionDerivedChange T (reductionCoefficientMap T d b a h)).map
              (reductionScalarComplexCounit T (completedReductionProjection T d b) P) ≫
            reductionScalarComplexCounit T (reductionCoefficientMap T d b a h)
              ((reductionChangeComplex T (completedReductionProjection T d b)).obj P) ≫
            DerivedCategory.Q.map
              (reductionBalance T (completedReductionProjection T d b)
                (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
                (completedReductionProjection_comp T d b a h) P) := by
  exact derivedReductionComposition T (completedReductionProjection T d b)
    (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
    (completedReductionProjection_comp T d b a h)

/-- The canonical normalization natural transformation, fixed by its K-flat formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionDerivedNormalization (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    reductionDerivedChange T (completedReductionProjection T d b) ⋙
      reductionDerivedChange T (reductionCoefficientMap T d b a h) ⟶
        reductionDerivedChange T (completedReductionProjection T d a) :=
  (completedReductionDerivedNormalization_exists T d b a h).choose

/-- The universal counit of the reduction tower, selected together with its left derived
functor and hence determining all resolution comparisons.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def coherenceReductionTowerCounit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    DerivedCategory.Qh ⋙ completedReductionTower T d ⟶
      completedReductionHomotopyFunctor T d :=
  (completedReductionTower_exists T d).choose_spec.choose

/-- The canonical reduction tower is universal, triangulated and computed on K-flat models.
Source: blueprint order 1239; Stacks Tags 06XN, 06YS and 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the total left derived functor has the universal right Kan extension counit.
The published existence theorem completedReductionTower_exists identifies this pair
with the exact homotopy functor on K-flat representatives. It therefore transports the
shift and triangle structure and makes the counit invertible on these representatives.
Uniqueness of derived pairs makes these the canonical resolution comparisons. -/
theorem completedReductionTower_properties (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionTower T d).IsLeftDerivedFunctor (coherenceReductionTowerCounit T d)
        (HomotopyCategory.quasiIso (reductionModules T (completedReductionCoefficient T d))
          (.up ℤ)) ∧
      (∃ (_ : (completedReductionTower T d).CommShift ℤ),
        (completedReductionTower T d).IsTriangulated) ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := completedReductionCoefficient T d) P →
          IsIso ((coherenceReductionTowerCounit T d).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  exact (completedReductionTower_exists T d).choose_spec.choose_spec

attribute [local irreducible] completedReductionTower
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

/-- The tower counit on a complex, using canonical localization factorizations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTowerComplexCounit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ) :
    (completedReductionTower T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj P) :=
  reductionComplexCounit (completedReductionModuleTowerFunctor T d)
    (completedReductionTower T d) (coherenceReductionTowerCounit T d) P

private theorem transpose_app
    {J A B : Type*} [Category J] [Category A] [Category B]
    {R : A ⥤ B} {U : B ⥤ A} (a : R ⊣ U)
    (F : J ⥤ A) (G : J ⥤ B) (f : F ⋙ R ⟶ G) (X : J) :
    (((a.whiskerRight J).homEquiv F G) f).app X =
      a.homEquiv (F.obj X) (G.obj X) (f.app X) := by
  dsimp [Adjunction.homEquiv]
  simp

private theorem transpose_symm_app
    {J A B : Type*} [Category J] [Category A] [Category B]
    {R : A ⥤ B} {U : B ⥤ A} (a : R ⊣ U)
    (F : J ⥤ A) (G : J ⥤ B) (f : F ⟶ G ⋙ U) (X : J) :
    (((a.whiskerRight J).homEquiv F G).symm f).app X =
      (a.homEquiv (F.obj X) (G.obj X)).symm (f.app X) := by
  dsimp [Adjunction.homEquiv]
  simp

private theorem kan_postcompose_rightAdjoint
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (Q : C ⥤ D) (E : C ⥤ B) (F : D ⥤ B) (ε : Q ⋙ F ⟶ E)
    [F.IsRightKanExtension ε] {R : A ⥤ B} {U : B ⥤ A} (a : R ⊣ U) :
    (F ⋙ U).IsRightKanExtension
      ((Functor.associator Q F U).inv ≫ whiskerRight ε U) := by
  let e := (Functor.associator Q F U).inv ≫ whiskerRight ε U
  let b (K : D ⥤ A) (β : Q ⋙ K ⟶ E ⋙ U) : Q ⋙ (K ⋙ R) ⟶ E :=
    (Functor.associator Q K R).inv ≫
      ((a.whiskerRight C).homEquiv (Q ⋙ K) E).symm β
  let g (K : D ⥤ A) (β : Q ⋙ K ⟶ E ⋙ U) : K ⟶ F ⋙ U :=
    ((a.whiskerRight D).homEquiv K F) (F.liftOfIsRightKanExtension ε (K ⋙ R) (b K β))
  have hg (K : D ⥤ A) (β : Q ⋙ K ⟶ E ⋙ U) : whiskerLeft Q (g K β) ≫ e = β := by
    ext X
    change ((g K β).app (Q.obj X)) ≫ (𝟙 _ ≫ U.map (ε.app X)) = β.app X
    rw [Category.id_comp]
    rw [show (g K β).app (Q.obj X) = _ from transpose_app a K F _ (Q.obj X)]
    rw [← a.homEquiv_naturality_right]
    rw [F.liftOfIsRightKanExtension_fac_app]
    change a.homEquiv _ _ (𝟙 _ ≫ _) = _
    rw [Category.id_comp, transpose_symm_app]
    exact Equiv.apply_symm_apply _ _
  refine ⟨⟨IsTerminal.ofUniqueHom
    (fun K ↦ CostructuredArrow.homMk (g K.left K.hom) (hg K.left K.hom)) ?_⟩⟩
  intro K m
  apply CostructuredArrow.hom_ext
  apply ((a.whiskerRight D).homEquiv K.left F).symm.injective
  apply F.hom_ext_of_isRightKanExtension ε
  ext X
  apply (a.homEquiv _ _).injective
  dsimp only [NatTrans.comp_app, whiskerLeft_app, CostructuredArrow.homMk_left]
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right]
  simp only [Functor.comp_obj, transpose_symm_app, Equiv.apply_symm_apply]
  have hm := NatTrans.congr_app m.w X
  have hn := NatTrans.congr_app (hg K.left K.hom) X
  change m.left.app (Q.obj X) ≫ (𝟙 _ ≫ U.map (ε.app X)) = K.hom.app X at hm
  change (g K.left K.hom).app (Q.obj X) ≫ (𝟙 _ ≫ U.map (ε.app X)) = K.hom.app X at hn
  simp only [Category.id_comp] at hm hn
  exact hm.trans hn.symm

private theorem scalarDerivedAdjunction_exists (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    Nonempty (reductionDerivedChange T φ ⊣ reductionDerivedRestrict T φ) := by
  let h := reductionChange_obj_eq T φ
  have hm {M N : reductionModules T R} (f : M ⟶ N) :
      (reductionChange T φ).map f = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm :=
    reductionChange_map_eq T φ f
  obtain ⟨_, _, hex⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (J := ProEt.topology T) φ
  obtain ⟨_, _, hder⟩ := hex (reductionChange T φ) h hm
  obtain ⟨adj, _⟩ := hder (reductionDerivedChange T φ) (reductionDerivedCounit T φ)
    (reductionDerivedUniversal T φ)
  exact ⟨adj⟩

private theorem towerCounit_isIso (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P) :
    IsIso (completedReductionTowerComplexCounit T d P) := by
  have : IsIso ((coherenceReductionTowerCounit T d).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (completedReductionTower_properties T d).2.2 P hP
  dsimp only [completedReductionTowerComplexCounit, reductionComplexCounit]
  infer_instance

private theorem whisker_cast_heq
    {A B : Type*} [Category A] [Category B] {K G G' : A ⥤ B}
    (h : G' = G) (β : K ⟶ G') (P : A) :
    HEq ((β ≫ eqToHom h).app P) (β.app P) := by
  subst G'
  exact heq_of_eq (by simp)

private theorem derivedKanComparison
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D]
    (L K : DerivedCategory B ⥤ D) (G G' : CochainComplex B ℤ ⥤ D)
    (α : DerivedCategory.Q ⋙ L ⟶ G) (β : DerivedCategory.Q ⋙ K ⟶ G')
    (h : G' = G) [L.IsRightKanExtension α]
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ,
      ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S P ∧ QuasiIso p)
    (hα : ∀ P, S P → IsIso (α.app P))
    (hβ : ∀ P, S P → IsIso (β.app P)) :
    ∃! τ : K ⟶ L, IsIso τ ∧ ∀ P, S P →
      HEq (τ.app (DerivedCategory.Q.obj P) ≫ α.app P) (β.app P) := by
  let β' := β ≫ eqToHom h
  have hb (P : CochainComplex B ℤ) : HEq (β'.app P) (β.app P) :=
    whisker_cast_heq h β P
  let τ := L.liftOfIsRightKanExtension α K β'
  have ht (P : CochainComplex B ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ α.app P = β'.app P :=
    L.liftOfIsRightKanExtension_fac_app α K β' P
  refine ⟨τ, ⟨?_, ?_⟩, ?_⟩
  · apply derived_natTrans_isIso K L S hres τ
    intro P hP
    have := hα P hP
    have := hβ P hP
    have : IsIso (β'.app P) := by dsimp only [β', NatTrans.comp_app]; infer_instance
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ α.app P) := (ht P).symm ▸ this
    exact IsIso.of_isIso_comp_right _ (α.app P)
  · intro P _
    exact (heq_of_eq (ht P)).trans (hb P)
  · intro τ' hτ'
    apply derived_natTrans_ext K L S hres
    intro P hP
    have := hα P hP
    apply (cancel_mono (α.app P)).1
    have he := (hτ'.2 P hP).trans (hb P).symm
    exact (eq_of_heq he).trans (ht P).symm

private theorem derivedEvaluationComparison
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {W : Type u₃} [Category.{v₃} W] [Abelian W] [HasDerivedCategory.{w₃} W]
    (F : B ⥤ D) [F.Additive] (LF : DerivedCategory B ⥤ DerivedCategory D)
    (εF : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor εF (HomotopyCategory.quasiIso B (.up ℤ))]
    (R₀ : D ⥤ B) [R₀.Additive] [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    (a : LF ⊣ R₀.mapDerivedCategory)
    (H₀ : B ⥤ W) [H₀.Additive] (LH : DerivedCategory B ⥤ DerivedCategory W)
    (εH : DerivedCategory.Qh ⋙ LH ⟶
      H₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (V₀ : W ⥤ B) [V₀.Additive] [PreservesFiniteLimits V₀] [PreservesFiniteColimits V₀]
    (hlevel : H₀.mapHomologicalComplex (.up ℤ) ⋙ V₀.mapHomologicalComplex (.up ℤ) =
      F.mapHomologicalComplex (.up ℤ) ⋙ R₀.mapHomologicalComplex (.up ℤ))
    (S₀ : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ,
      ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S₀ P ∧ QuasiIso p)
    (hFiso : ∀ P, S₀ P → IsIso (reductionComplexCounit F LF εF P))
    (hHiso : ∀ P, S₀ P → IsIso (reductionComplexCounit H₀ LH εH P)) :
    ∃! τ : LH ⋙ V₀.mapDerivedCategory ⟶ LF ⋙ R₀.mapDerivedCategory,
      IsIso τ ∧ ∀ P : CochainComplex B ℤ, S₀ P →
        HEq (τ.app (DerivedCategory.Q.obj P) ≫
          R₀.mapDerivedCategory.map (reductionComplexCounit F LF εF P) ≫
          R₀.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P))
        (V₀.mapDerivedCategory.map (reductionComplexCounit H₀ LH εH P) ≫
          V₀.mapDerivedCategoryFactors.hom.app
            ((H₀.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E := F.mapHomologicalComplex (.up ℤ)
  let R := R₀.mapHomologicalComplex (.up ℤ)
  let V := V₀.mapHomologicalComplex (.up ℤ)
  let H := H₀.mapHomologicalComplex (.up ℤ)
  let L := LF ⋙ R₀.mapDerivedCategory
  let K := LH ⋙ V₀.mapDerivedCategory
  let e := complexCounitNat F LF εF
  have := complexCounitNat_kan F LF εF
  have : LF.IsRightKanExtension e :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ e
      (HomologicalComplex.quasiIso _ (.up ℤ))
  have := kan_postcompose_rightAdjoint DerivedCategory.Q (E ⋙ DerivedCategory.Q) LF e a
  let f : (E ⋙ DerivedCategory.Q) ⋙ R₀.mapDerivedCategory ≅
      (E ⋙ R) ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft E R₀.mapDerivedCategoryFactors ≪≫
      (Functor.associator E R DerivedCategory.Q).symm
  let α : DerivedCategory.Q ⋙ L ⟶ (E ⋙ R) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ whiskerRight e R₀.mapDerivedCategory ≫ f.hom
  have hkan := kan_change_iso L (Iso.refl DerivedCategory.Q) f
    ((Functor.associator _ _ _).inv ≫ whiskerRight e R₀.mapDerivedCategory)
  have : L.IsRightKanExtension α := by
    have hi : whiskerRight (Iso.refl DerivedCategory.Q).inv L = 𝟙 _ := by
      ext X
      exact L.map_id _
    rw [hi] at hkan
    simpa only [α, Category.id_comp, Category.assoc] using hkan
  let eH := complexCounitNat H₀ LH εH
  let β : DerivedCategory.Q ⋙ K ⟶ (H ⋙ V) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ whiskerRight eH V₀.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft H V₀.mapDerivedCategoryFactors.hom ≫
      (Functor.associator _ _ _).inv
  have hα (P : CochainComplex B ℤ) :
      α.app P = R₀.mapDerivedCategory.map (reductionComplexCounit F LF εF P) ≫
        R₀.mapDerivedCategoryFactors.hom.app (E.obj P) := by
    change (𝟙 _ ≫ R₀.mapDerivedCategory.map (e.app P) ≫
      𝟙 _ ≫ R₀.mapDerivedCategoryFactors.hom.app (E.obj P) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id, e, complexCounitNat_app]
  have hβ (P : CochainComplex B ℤ) :
      β.app P = V₀.mapDerivedCategory.map (reductionComplexCounit H₀ LH εH P) ≫
        V₀.mapDerivedCategoryFactors.hom.app (H.obj P) := by
    change (𝟙 _ ≫ V₀.mapDerivedCategory.map (eH.app P) ≫
      𝟙 _ ≫ V₀.mapDerivedCategoryFactors.hom.app (H.obj P) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id, eH, complexCounitNat_app]
  have hαiso (P) (hP : S₀ P) : IsIso (α.app P) := by
    have := hFiso P hP
    rw [hα]
    infer_instance
  have hβiso (P) (hP : S₀ P) : IsIso (β.app P) := by
    have := hHiso P hP
    rw [hβ]
    infer_instance
  obtain ⟨τ, hτ, huniq⟩ := derivedKanComparison L K _ _ α β
    (congrArg (fun G ↦ G ⋙ DerivedCategory.Q) hlevel) S₀ hres hαiso hβiso
  refine ⟨τ, ⟨hτ.1, ?_⟩, ?_⟩
  · intro P hP
    simpa only [hα, hβ] using hτ.2 P hP
  · intro τ' hτ'
    apply huniq τ'
    refine ⟨hτ'.1, ?_⟩
    intro P hP
    simpa only [hα, hβ] using hτ'.2 P hP

attribute [local semireducible] completedReductionModuleTowerFunctor

/-- Derived tower evaluation is canonically restriction of the quotient object K_n.
The equation fixes this comparison on every K-flat representative by the actual tower
and scalar-extension counits; no arbitrary identification is chosen.
Source: blueprint order 1239, evaluation paragraph; Stacks Tags 015F and 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on a K-flat complex P both functors are computed by P tensor (P_n)_T with
its completion action. The two universal counits and exact evaluation identify that
same ordinary complex and all its maps. This gives the displayed comparison and its
naturality on K-flat representatives. Quasi-isomorphisms between these representatives
are inverted, so the comparison descends. Every object has a K-flat representative;
the displayed equality with invertible counits forces uniqueness and invertibility. -/
theorem completedReductionEvaluation_exists (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! τ : completedReductionTower T d ⋙
        reductionTowerDerivedEvaluation T
          (reductionModuleRing T (completedReductionCoefficient T d)) n ⟶
        reductionDerivedChange T (completedReductionProjection T d n) ⋙
          reductionDerivedRestrict T (completedReductionProjection T d n),
      IsIso τ ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            (reductionDerivedRestrict T (completedReductionProjection T d n)).map
              (reductionScalarComplexCounit T (completedReductionProjection T d n) P) ≫
            (reductionRestrict T
              (completedReductionProjection T d n)).mapDerivedCategoryFactors.hom.app
              ((reductionChangeComplex T (completedReductionProjection T d n)).obj P) =
          (reductionTowerDerivedEvaluation T
              (reductionModuleRing T (completedReductionCoefficient T d)) n).map
              (completedReductionTowerComplexCounit T d P) ≫
            (reductionTowerEvaluation T
              (reductionModuleRing T
                (completedReductionCoefficient T d)) n).mapDerivedCategoryFactors.hom.app
                  ((completedReductionComplexTowerFunctor T d).obj P) := by
  let S₀ (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (R := completedReductionCoefficient T d) P
  have hres (X : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ) :
      ∃ (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
        (p : P ⟶ X), S₀ P ∧ QuasiIso p := by
    obtain ⟨P, p, hk, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) X
    exact ⟨P, p, hk, hp⟩
  obtain ⟨τ, hτ, huniq⟩ := derivedEvaluationComparison
    (reductionChange T (completedReductionProjection T d n))
    (reductionDerivedChange T (completedReductionProjection T d n))
    (reductionDerivedCounit T (completedReductionProjection T d n))
    (reductionRestrict T (completedReductionProjection T d n))
    (scalarDerivedAdjunction_exists T (completedReductionProjection T d n)).some
    (completedReductionModuleTowerFunctor T d) (completedReductionTower T d)
    (coherenceReductionTowerCounit T d)
    (reductionTowerEvaluation T
      (reductionModuleRing T (completedReductionCoefficient T d)) n)
    (level_complex_eq T d n) S₀ hres
    (scalarCounit_isIso T (completedReductionProjection T d n)) (towerCounit_isIso T d)
  refine ⟨τ, ⟨hτ.1, ?_⟩, ?_⟩
  · intro P hP
    exact eq_of_heq (hτ.2 P hP)
  · intro τ' hτ'
    apply huniq τ'
    refine ⟨hτ'.1, ?_⟩
    intro P hP
    exact heq_of_eq (hτ'.2 P hP)

/-- The canonical evaluation comparison, fixed by its formula on K-flat representatives.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionEvaluation (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n ⟶
      reductionDerivedChange T (completedReductionProjection T d n) ⋙
        reductionDerivedRestrict T (completedReductionProjection T d n) :=
  (completedReductionEvaluation_exists T d n).choose

/-- The canonical evaluation comparison is invertible as a natural transformation.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the defining unique-existence theorem asserts invertibility of the selected
natural transformation. Apply its existence specification to its chosen witness
and take the invertibility conjunct. -/
@[instance]
theorem completedReductionEvaluation_isIso (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    IsIso (completedReductionEvaluation T d n) := by
  exact (completedReductionEvaluation_exists T d n).choose_spec.1.1

/-- The ambient derived category of modules over the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.derived {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) :=
  reductionDerivedCategory T (d.completedRing T)

/-- The strict tower category over the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.towers {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) :=
  reductionTowerCategory T (reductionModuleRing T (d.completedRing T))

/-- Finite reduction retains the quotient coefficient action.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.reduction {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) :=
  reductionDerivedChange T (d.projection T n)

end AlgebraicGeometry.Scheme
