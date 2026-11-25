/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperReductionBound
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete

/-! The integral constructible proper heart estimate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem complete_upper_of_levels
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (Y : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules ℓ E Y))
    (hK : IsDerivedComplete ℓ E Y K) (b : ℤ)
    (hb : ∀ n : ℕ, (AdicCompletion.integralLevel ℓ E Y K n).IsLE b) :
    K.IsLE (b + 1) := by
  obtain ⟨P, hP, ⟨e⟩, hcomplete⟩ := hK
  obtain ⟨p, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit ℓ E Y K P hP e
  have : IsIso (AdicCompletion.completionMap ℓ E Y K P e) := by
    dsimp [AdicCompletion.completionMap]
    infer_instance
  have hprod : (∏ᶜ AdicCompletion.integralLevel ℓ E Y K).IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro q hq
    have hP := isLimitOfPreserves (DerivedCategory.homologyFunctor _ q)
      (productIsProduct (AdicCompletion.integralLevel ℓ E Y K))
    apply (IsZero.iff_id_eq_zero _).2
    apply hP.hom_ext
    intro n
    exact (DerivedCategory.isZero_of_isLE _ b q hq (hX := hb n.as)).eq_of_tgt _ _
  have hprod' : (∏ᶜ AdicCompletion.integralLevel ℓ E Y K).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE_of_le _ b (b + 1) (by omega)
  have hshift : ((∏ᶜ AdicCompletion.integralLevel ℓ E Y K)⟦(-1 : ℤ)⟧).IsLE
      (b + 1) := DerivedCategory.TStructure.t.isLE_shift _ b (-1) (b + 1) (by omega)
  have hroos : (DerivedCategory.Q.obj (AdicCompletion.roos ℓ E Y P)).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang _ hT)
      (b + 1) hshift hprod'
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (AdicCompletion.completionMap ℓ E Y K P e)).symm (b + 1)

/-- The integral constructible proper heart estimate over a Noetherian source, with no base
field. Derived completeness of the image comes from integral direct-image limits and the
residue criterion; the finite reductions use the Noetherian finite-reduction bound. -/
theorem integralProperConstructibleHeartBound_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X N →
      ((CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * (d : ℤ) + 1) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let A := pulledBackModuleObjects Λ X
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := by dsimp [e]; infer_instance
  have : IsMonHom e.inv := by dsimp [e]; infer_instance
  let T (Z : Scheme.{u}) : pulledBackModuleObjects Λ Z ⥤
      AdicCompletion.Modules ℓ (ULift.{u} E.val) Z :=
    Mod.comap (coefficientMap e.inv Z)
  have (Z : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  intro N hN
  let K := (DerivedCategory.singleFunctor A 0).obj N
  have hK : constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ
      (ULift.{u} E.val)) X ((T X).mapDerivedCategory.obj K) := by
    have h := constantModelConstructible_single Λ X N hN
    refine ⟨(T X).bounded_mapDerivedCategory_obj h.1, fun q ↦ ?_⟩
    exact constructible_iso (((T X).mapDerivedCategoryHomologyFunctorIso q).app K)
      ((constantModel_comap_iff e.inv X _).2 (h.2 q))
  have hcomplete : IsDerivedComplete ℓ (ULift.{u} E.val) Y
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) p).obj
          ((T X).mapDerivedCategory.obj K)) := by
    obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits ℓ (ULift.{u} E.val) p
    let := hχ
    exact (hpush _).1
      (((internal_integral_residue_criterion ℓ (ULift.{u} E.val) X).1 _).mp hK).1
  have hb := complete_upper_of_levels ℓ (ULift.{u} E.val) Y _ hcomplete
    (2 * (d : ℤ)) (fun n ↦ by
      simpa only [zero_add] using integralProperReductionBound_of_isNoetherian ℓ (ULift.{u} E.val)
        p d hd _ hK 0 ((T X).isLE_mapDerivedCategory_obj K 0) n)
  have hi := (CondensedRing.derivedComapLowerStarIso e.inv p).app K
  rw [DerivedCategory.isLE_iff] at hb ⊢
  intro q hq
  apply (T Y).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  exact (hb q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso hi)

set_option linter.unusedVariables false in
/-- Proper direct image of a constructible integral sheaf vanishes above 2d+1. -/
theorem integralProperConstructibleHeartBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X N →
      ((CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * (d : ℤ) + 1) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  exact integralProperConstructibleHeartBound_of_isNoetherian ℓ E p d hd

end AlgebraicGeometry.ProEtale
