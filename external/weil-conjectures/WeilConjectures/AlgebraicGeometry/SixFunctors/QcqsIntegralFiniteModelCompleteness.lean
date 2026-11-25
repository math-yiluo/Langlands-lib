/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence

import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Category.Profinite.AsLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.FiniteStrataCompletion.FiniteStrataCompletionDetection
import WeilConjectures.AlgebraicGeometry.FiniteScalarCompletion.FiniteScalarLocalModelComplete
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Completeness and classical reductions of qcqs integral finite-model inputs

The scheme is arbitrary qcqs. The integral ring carries its spectral norm topology.
The completion predicate uses the specified strict-tower augmentation. Finite reductions
are formed by the recorded derived extension along the actual quotient homomorphism.
The ordinary coordinate condition retains the comparison equivalence and etale-origin pair.

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5--6.6
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits

attribute [local irreducible] IsDerivedComplete

private theorem complete_triangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (V : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete l E V) ∧
      ObjectProperty.IsTriangulated (IsDerivedComplete l E V) := by
  obtain ⟨data, hdata, a, F, c, κ, sF, hF, ha, hc, hψ, hcomplete, hshift, htriangle⟩ :=
    CompletionTriangle.completion_triangle_comparison l E V
  let := hF
  have hi : ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete l E V) := by
    refine ⟨fun e h ↦ (hcomplete _).2 ?_⟩
    exact (NatTrans.isIso_app_iff_of_iso c e).mp ((hcomplete _).1 h)
  let := hi
  have : ObjectProperty.IsStableUnderShift (IsDerivedComplete l E V) ℤ := ⟨fun r ↦ ⟨by
    intro K hK
    have : IsIso (c.app K) := (hcomplete _).1 hK
    apply (hcomplete _).2
    have : IsIso (c.app (K⟦r⟧) ≫
        (Functor.commShiftIso (self := sF) F r).hom.app K) := by
      rw [hshift]
      infer_instance
    exact IsIso.of_isIso_comp_right (c.app (K⟦r⟧))
      ((Functor.commShiftIso (self := sF) F r).hom.app K)⟩⟩
  have : ObjectProperty.IsTriangulatedClosed₂ (IsDerivedComplete l E V) :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (by
      intro T hT h₁ h₃
      obtain ⟨hFT, γ, hγ₁, hγ₂, hγ₃⟩ := htriangle T hT
      apply (hcomplete _).2
      rw [← hγ₂]
      apply isIso₂_of_isIso₁₃ γ hT hFT
      · rw [hγ₁]; exact (hcomplete _).1 h₁
      · rw [hγ₃]; exact (hcomplete _).1 h₃)
  refine ⟨hi, { exists_zero := ⟨0, isZero_zero _, (hcomplete _).2 ?_⟩ }⟩
  exact (isZero_zero _).isIso (F.map_isZero (isZero_zero _)) _

private theorem complete_scalar_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E))
    (hP : Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P) :
    IsDerivedComplete l E T ((DerivedCategory.singleFunctor _ 0).obj
      ((DerivedNakayama.pullback l E T).obj P)) := by
  rw [← DerivedCategory.Q_obj_single_obj]
  exact (FiniteScalarCompletion.finite_scalar_local_model_complete l E T).2.1 P hP

private theorem complete_cover_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V)
    (M : AdicCompletion.Modules l E V)
    (h : ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
      Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).obj M) ≅
        (DerivedNakayama.pullback l E T).obj P)) :
    IsDerivedComplete l E T ((FiniteStrataCompletion.pull l E f).obj
      ((FiniteStrataCompletion.pull l E g).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  have := (complete_triangulated l E T).1
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) g
  let G := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  apply ObjectProperty.prop_of_iso (IsDerivedComplete l E T)
    (G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj M) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eP).symm
  exact complete_scalar_single l E T P hP

private theorem complete_stratified_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V) (S : Scheme.Stratification V)
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (hC : ∀ (a : Fin S.n) (i : (C a).I₀),
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E),
        Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
        Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
          ((C a).f i)).obj
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (S.immersion a)).obj M) ≅
            (DerivedNakayama.pullback l E ((C a).X i)).obj P)) :
    IsDerivedComplete l E V ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let S' : Scheme.FiniteLocallyClosedStratification V :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  apply ((FiniteStrataCompletion.finite_strata_completion_detection l E S' C
    S.isConstructible_stratum).1 _).1.mpr
  intro a i
  exact complete_cover_single l E ((C a).f i) (S.immersion a) M (hC a i)

private theorem models_on_qcqs
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    IsConstantModelConstructible Λ V M ↔ IsFiniteConstantStratified Λ V M := by
  unfold IsConstantModelConstructible
  rw [ite_eq_left (show CompactSpace V ∧ QuasiSeparatedSpace V from
    ⟨inferInstance, inferInstance⟩)]

private theorem complete_sheaf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M) :
    IsDerivedComplete l E V ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨S, hS⟩ := (models_on_qcqs (DerivedNakayama.integerRing l E) V M).mp hM
  obtain ⟨C, hC⟩ := Classical.axiomOfChoice hS
  exact complete_stratified_single l E V M S C hC

end AlgebraicGeometry.ProEtale
