/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement

/-!
# The completed coefficient ring on the canonical small site

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: def-weil-pbc-completed-cech-site-transport).

The site, module, derived and scalar transports are constructed here. The regular-module
unit is the transported section 1. The finite Koszul comparison is proved in its own
module, so its coefficient and tensor lemmas can import these constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The pro-etale category with its morphisms lifted to the coefficient universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
abbrev completedCechSite := AsSmall.{0} X.ProEt

/-- The canonical equivalence with the category whose Hom universe has been lifted.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
abbrev completedCechSiteEquiv : X.ProEt ≌ completedCechSite X := AsSmall.equiv

/-- The topology induced along the inverse of the canonical site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
abbrev completedCechTopology :=
  (completedCechSiteEquiv X).inverse.inducedTopology (ProEt.topology X)

/-- The actual completed ring sheaf pulled to the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
abbrev completedCechRing : Sheaf (completedCechTopology X) CommRingCat.{u + 1} :=
  ((completedCechSiteEquiv X).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    (completedCechTopology X) (ProEt.topology X)).obj (pbcAdicCompletion X d)

/-- The module-sheaf equivalence induced by the canonical ringed-site equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
def completedCechModulesEquiv :
    pbcModules X (pbcAdicCompletion X d) ≌ ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d)) := by
  let e := completedCechSiteEquiv X
  let J := ProEt.topology X
  let K := completedCechTopology X
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (pbcAdicCompletion X d)
  let R' : Sheaf K RingCat.{u + 1} :=
    (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  let φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) R.obj⟩
  let ψ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R := 𝟙 _
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) R'.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.inverse.map (e.counit.app U.unop)).op =
      R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
    rw [e.unitInv_app_inverse]
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
    apply NatTrans.ext
    funext U
    change R.obj.map (e.unitInv.app U.unop).op ≫
      (𝟙 _ ≫ R.obj.map (e.unit.app U.unop).op) = 𝟙 _
    rw [Category.id_comp, ← R.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
    exact R.obj.map_id _
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} e φ ψ h₁ h₂).symm

/-- The standard derived category in the original ambient derived universe.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
instance : HasDerivedCategory.{u + 2} (ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
    ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedCechRing X d))) := HasDerivedCategory.standard _

/-- The exact module equivalence is additive because it preserves products and zero.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
instance : (completedCechModulesEquiv X d).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The equivalence induced on unbounded derived categories by the module equivalence.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
def completedCechDerivedEquiv : PbcCompletedDerived X d ≌
    ringedSiteDerived.{u + 1, u + 2} (completedCechRing X d) :=
  (completedCechModulesEquiv X d).mapDerivedCategory

/-- The compatible-residue scalar map, followed by the fixed coefficient comparison.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
def completedCechScalarMap :
    (Functor.const (completedCechSite X)ᵒᵖ).obj (CommRingCat.of A) ⟶
      (completedCechRing X d).obj :=
  Functor.whiskerLeft (completedCechSiteEquiv X).inverse.op
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (adicDatumScalar X (intrinsicPresentationDatum d)).hom ≫
        (pbcCompletedComparison X d).hom.hom)

/-- The actual compatible-residue scalar as a global section on the canonical small site.
Source: Stacks, Tag 0A0E, with the canonical equivalence of ringed sites
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
def completedCechScalar (a : A) :
    ((completedCechRing X d).obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections := by
  refine ⟨fun U ↦ (completedCechScalarMap X d).app U a, ?_⟩
  intro U V f
  exact congrArg (fun g ↦ g a) ((completedCechScalarMap X d).naturality f).symm

/-- The strict-tower derived category in the same ambient universe.
Source: Stacks, Tag 0941
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
instance : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤
    ringedSiteModules.{u + 1, u + 1, u + 1, u + 1}
      ((sheafCompose (completedCechTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedCechRing X d))) := HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The transported regular-module unit, given by the section 1.
Source: Stacks Project, Tag 03DA, restriction along a ring isomorphism and site equivalence
(blueprint: def-weil-pbc-completed-cech-site-transport). -/
def completedCechCoefficientUnit :
    SheafOfModules.unit ((sheafCompose (completedCechTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (completedCechRing X d)) ⟶
    (intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor).obj
      (SheafOfModules.unit ((adicLisseForget X).obj
        (adicDatumRing X (intrinsicPresentationDatum d)))) := by
  refine (SheafOfModules.unitHomEquiv _).symm ?_
  refine ⟨fun U ↦ (1 : (adicDatumRing X (intrinsicPresentationDatum d)).obj.obj
    ((completedCechSiteEquiv X).inverse.op.obj U)), ?_⟩
  intro U V f
  exact (adicDatumRing X (intrinsicPresentationDatum d)).obj.map
    ((completedCechSiteEquiv X).inverse.op.map f) |>.hom.map_one

end AlgebraicGeometry.Scheme
