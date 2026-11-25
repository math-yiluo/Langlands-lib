/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Extension of the ordinary scalar comparison from the rank-one quotient

Source: Stacks Project, Tags 093J, 093M and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing

private theorem moduleNatTrans_ext_regular
    {R : Type t} [CommRing R] {C : Type*} [Category C]
    (F G : ModuleCat.{t} R ⥤ C) [PreservesColimitsOfSize.{t, t} F]
    (a b : F ⟶ G)
    (h : a.app (ModuleCat.of R R) = b.app (ModuleCat.of R R)) : a = b := by
  have : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  apply NatTrans.ext
  funext N
  let P := (ModuleCat.free R).obj N
  let q : P ⟶ N := ModuleCat.freeDesc (↾fun x : N ↦ x)
  have : Epi q := (ModuleCat.epi_iff_surjective q).2
    (fun x ↦ ⟨ModuleCat.freeMk x, ModuleCat.freeDesc_apply _ x⟩)
  apply (cancel_epi (F.map q)).mp
  rw [a.naturality, b.naturality]
  have hP : a.app P = b.app P := by
    apply (isColimitOfPreserves F (ModuleCat.finsuppCoconeIsColimit R R N)).hom_ext
    rintro ⟨x⟩
    let ι : ModuleCat.of R R ⟶ P := ModuleCat.ofHom
      (Finsupp.lsingle x)
    have ha := a.naturality ι
    have hb := b.naturality ι
    exact ha.trans ((congrArg (fun k ↦ k ≫ G.map ι) h).trans hb.symm)
  rw [hP]

private theorem ordinaryTarget_colimits
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (W : X.ProEt) (n : ℕ) :
    PreservesColimitsOfSize.{t, t} (finitePerfectAdicOrdinaryScalarTarget X d W n) := by
  have : PreservesColimitsOfSize.{t, t} (ModuleCat.uliftFunctor.{t + 1, t} A) := by
    let U := forget₂ (ModuleCat.{t + 1} A) AddCommGrpCat.{t + 1}
    have : PreservesColimitsOfSize.{t, t}
        (ModuleCat.uliftFunctor.{t + 1, t} A ⋙ U) := by
      change PreservesColimitsOfSize.{t, t}
        (forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t} ⋙
          AddCommGrpCat.uliftFunctor.{t + 1, t})
      infer_instance
    have : ReflectsColimitsOfSize.{t, t} U :=
      { reflectsColimitsOfShape := fun {_} _ ↦
          reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesColimits_of_reflects_of_preserves _ U
  let P := siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)
  have : PreservesColimitsOfSize.{t, t} P := by
    constructor
    intro K _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  have : PreservesColimitsOfSize.{t, t} (koszulConstantFunctor X A) := by
    unfold koszulConstantFunctor
    infer_instance
  have : PreservesColimitsOfSize.{t, t} (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  have : PreservesColimitsOfSize.{t, t} (finitePerfectAdicConstant X A) := by
    change PreservesColimitsOfSize.{t, t}
      (ModuleCat.uliftFunctor.{t + 1, t} A ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom ⋙ koszulConstantFunctor X A)
    infer_instance
  have : (completedAdicScalarExtension X d).Additive :=
    (completedAdicScalarExtensionData X d).choose_spec.choose_spec.choose_spec.choose
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (completedAdicScalar X d)
  obtain ⟨adj, _⟩ := h (completedAdicScalarExtension X d)
    (completedAdicScalarExtensionData X d).choose_spec.choose
    (fun f ↦ (completedAdicScalarExtensionData X d).choose_spec.choose_spec.choose f)
  have : PreservesColimitsOfSize.{t, t} (completedAdicScalarExtension X d) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{t, t}
      (ModuleCat.restrictScalars.{t} (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) :=
    (ModuleCat.restrictCoextendScalarsAdj.{t, t, t}
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{t, t}
      (SheafOfModules.overFunctor (completedAdicRing X d) W) := by
    exact (SheafOfModules.overPushforwardOverAdj
      (R := completedAdicRing X d) W).leftAdjoint_preservesColimits
  unfold finitePerfectAdicOrdinaryScalarTarget finitePerfectAdicScalarModelOrdinary
  infer_instance

/-- A rank-one ordinary scalar comparison extends to every quotient module.

Source: Stacks Project, Tags 093J and 093M; Tag 03CY for finite presentations.
(blueprint: new-s3-finite-perfect-adic-ordinary-scalar-compatibility)

Proof: both ordinary functors are exact and preserve finite coproducts.  A
finite presentation of a quotient module by free modules reduces the desired
square to the rank-one square on its generators; the completed projection
formula identifies the two maps there.  Cokernels and naturality then descend
the equality to the presented module.  The same argument handles zero modules
and empty charts.
-/
theorem finitePerfectAdicOrdinaryScalar_compatibility
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    (e : ∀ n : ℕ, finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
      finitePerfectAdicOrdinaryScalarTarget X d W n)
    (hunit : ∀ (n : ℕ),
      (e (n + 1)).hom.app
          ((ModuleCat.restrictScalars
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj
            (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
              (A ⧸ d.ideal ^ (n + 1)))) ≫
        (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1))) =
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1))) ≫
        (e n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1)))) :
    ∀ (n : ℕ) (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))),
      (e (n + 1)).hom.app
          ((ModuleCat.restrictScalars
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj N) ≫
        (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app N =
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app N ≫
        (e n).hom.app N := by
  -- Arbitrary modules need arbitrary free coproducts, rather than finite presentations.
  intro n N
  let Q := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let F := Q ⋙ finitePerfectAdicOrdinaryScalarSource X d V U W f (n + 1)
  let G := finitePerfectAdicOrdinaryScalarTarget X d W n
  let a : F ⟶ G := whiskerLeft Q (e (n + 1)).hom ≫
    (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom
  let b : F ⟶ G := (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom ≫
    (e n).hom
  have : PreservesColimitsOfSize.{t, t} G := ordinaryTarget_colimits X d W n
  have : PreservesColimitsOfSize.{t, t} F := preservesColimits_of_natIso
    ((finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n) ≪≫ e n).symm
  have hab : a = b := moduleNatTrans_ext_regular F G a b (hunit n)
  exact NatTrans.congr_app hab N

end AlgebraicGeometry.Scheme
