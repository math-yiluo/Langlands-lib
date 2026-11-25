/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
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
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionEvaluation
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionCoherence
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection

/-! # Constant coefficients and ordinary étale system compact support

Source: Zheng, Theorem 2.18(2), Construction 2.26, Constructions 5.14--5.15,
Lemma 5.16; Stacks Project, Tag 0GL6
(blueprint: lem-pur-etale-system-coefficient-projection).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

private theorem projection_transpose {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} (t : Theory c l)
    {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    (M : Derived X B.rings) :
    (t.scalarY a).adjunction.homEquiv _ _ ((t.q a).app M) =
      (t.support B).F.map ((t.scalarX a).adjunction.unit.app M) ≫
        (t.restriction a).iso.inv.app ((t.scalarX a).model.T.obj M) := by
  exact (unit_mateEquiv_symm (t.scalarX a).adjunction (t.scalarY a).adjunction
    (TwoSquare.mk _ _ _ _ (t.restriction a).iso.inv) M).symm

private theorem level_jointly_reflects (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    JointlyReflectIsomorphisms (level W B) where
  isIso {M N} h hh := by
    have : IsIso
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map h) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro U
      have := hh U.unop.1
      have hs : IsIso (((level W B U.unop.1).map h).hom.app (op U.unop.2)) :=
        inferInstance
      have hb := (ConcreteCategory.isIso_iff_bijective
        (((level W B U.unop.1).map h).hom.app (op U.unop.2))).1 hs
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective (fun x ↦ h.val.app U x) at hb ⊢
      exact hb
    exact isIso_of_reflects_iso h
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

private theorem compact_scalar_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    IsIso (compactScalarMap a c) := by
  suffices ∀ M, IsIso ((compactScalarMap a c).app M) from
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro M
  have := proper_scalarMate_isIso a c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  change IsIso ((scalarMate a c.g).app _ ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((ExceptionalCoefficients.openIso a c.i).hom.app M))
  infer_instance

private theorem projection_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} (t : Theory c l)
    {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) : IsIso (t.q a) := by
  suffices ∀ M, IsIso ((t.q a).app M) from
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro M
  let : ∀ n, (level Y C.rings n).Additive := fun n ↦ (t.evaluationY C n).additive
  let : ∀ n, PreservesFiniteLimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).limits
  let : ∀ n, PreservesFiniteColimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).colimits
  apply (Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (level_jointly_reflects Y C.rings)).isIso_iff _ |>.2
  intro n
  have := B.finite n
  have := compact_scalar_isIso (a.app (op n)).hom c
  have hi : IsIso
      ((scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.inv.app M) ≫
        (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
        (t.evaluationY C n).E.map ((t.q a).app M) ≫
        (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
            ((t.scalarEvaluationX a n).iso.hom.app M)) := by
    rw [etaleSystemProjection_evaluation c l t B C a n M]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi

end AlgebraicGeometry.Etale.SystemProjection
