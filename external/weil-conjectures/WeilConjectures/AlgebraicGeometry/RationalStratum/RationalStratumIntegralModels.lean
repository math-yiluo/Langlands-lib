/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalStratum.RationalStratumIntegralModelBasic
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedPieces
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralConstructibleComparison
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Lisse.LisseEConstructibleIntegralLattice
import WeilConjectures.AlgebraicGeometry.ContinuousFiltration.ContinuousFiltrationAdmissibleStrata
import WeilConjectures.AlgebraicGeometry.RationalStratum.IntegralPieceCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiniteFreeCriterion
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Filtration quotients with completed integral models

## References

* Bhatt--Scholze, Definitions 6.8.6 and 6.8.10, Proposition 6.8.11(3), Lemma 6.8.13 and Proposition
  6.8.14(2), pp. 60--62
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.RationalStratum

/-- Constructible rational sheaves have finite filtrations with genuine completed
integral models for the open/closed stratum quotients. IsCompletedModel retains
completeness, uniform constructible reductions and compatible etale-origin witnesses.
The integral sheaves are constructible; they need not be lisse or torsion-free. -/
theorem exists_filtration_integral_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (F : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (_hF : IsContinuousConstructible X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) F) :
    ∃ (m : ℕ)
      (H : Fin (m + 1) → SheafOfModules.{u + 1}
        (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
      (a : ∀ k, H k ⟶ F) (d : ∀ k : Fin m, H k.castSucc ⟶ H k.succ),
      (∀ k, Mono (a k)) ∧ IsZero (H 0) ∧ IsIso (a (Fin.last m)) ∧
      (∀ k : Fin m, d k ≫ a k.succ = a k.castSucc) ∧
      (∀ k : Fin m, Mono (d k)) ∧
      ∃ (U : Fin m → X.ProEt) (S : Fin m → Scheme.{u})
        (t : ∀ k : Fin m, S k ⟶ (U k).left)
        (hS : ∀ k : Fin m, IsNoetherian (S k))
        (L : ∀ k : Fin m, SheafOfModules.{u + 1}
          (latticeModuleRing (S k) (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
        (N : ∀ k : Fin m, SheafOfModules.{u + 1}
          (latticeModuleRing (S k) (latticeCoefficientIntegers l E))),
        (∀ k, IsOpenImmersion (U k).hom ∧ QuasiCompact (U k).hom ∧
          QuasiSeparated (U k).hom ∧ IsClosedImmersion (t k) ∧ IsReduced (S k)) ∧
        (∀ k, (∃ n : ℕ, topologicalKrullDim (S k) ≤ n) ∧
          ∀ x : S k, IsUnit (l : (S k).presheaf.stalk x)) ∧
        (∀ k, (L k).IsFiniteLocallyFree) ∧
        (∀ k, @IsContinuousConstructible (S k)
          (@IsNoetherian.noetherianSpace (S k) (hS k)) (latticeCoefficientIntegers l E)
          inferInstance inferInstance inferInstance (N k)) ∧
        (∀ k, IsContinuousConstructible X (latticeCoefficientIntegers l E)
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k))) ∧
        (∀ k, IsCompletedModel l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k))) ∧
        ∃ (α : ∀ k, integralModelRationalize l E (S k) (N k) ≅ L k)
          (_q : ∀ k, cokernel (d k) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj (L k))
          (e : ∀ k, integralModelRationalize l E X
              ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
                (integralModelRationalize l E (S k) (N k))),
          (∀ k, IsNormalizedComparison l E (U k) (t k) (N k) (e k)) ∧
          ∃ β : ∀ k, integralModelRationalize l E X
              ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj (L k),
            ∀ k, β k = e k ≪≫ (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).mapIso (α k) := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let hnorm : NormedAlgebra ℚ_[l] K := ⟨fun a x ↦ by
    change spectralNorm ℚ_[l] E (a • x.ofAbs) ≤
      ‖a‖ * spectralNorm ℚ_[l] E x.ofAbs
    exact (spectralNorm_smul a (Algebra.IsAlgebraic.isAlgebraic x.ofAbs)).le⟩
  have hfinite : FiniteDimensional ℚ_[l] K := Module.Finite.equiv
    (WithAbs.linearEquiv ℚ_[l] (Padic.coefficientExtensionAbsoluteValue l E)).symm
  have hfree : ∃ s : X.FiniteLocallyClosedStratification, ∀ j : Fin s.n,
      ((ContinuousFiltration.pull l K (s.immersion j)).obj F).IsFiniteLocallyFree := by
    obtain ⟨s, hs⟩ := _hF
    refine ⟨s.toFiniteLocallyClosed, fun j ↦ ?_⟩
    change (continuousModulePullback (s.immersion j) K F).IsFiniteLocallyFree
    apply (finiteLocalModels_iff (s.domain j) K _).mp
    have hm (P : ModuleCat.{u + 1} (ULift.{u + 1} K)) :
        continuousCoefficientModule (s.domain j) K P =
          (model (s.domain j) K).obj P :=
      (Scheme.reductionChange_obj_eq (s.domain j)
        (continuousCoefficientConstantMap (s.domain j) K) _).symm
    dsimp only [K] at hm ⊢
    simpa only [hm] using hs j
  obtain ⟨_, _, _, _, m, V, hV, hV0, hVlast, S, t, ht, hgeomV, hgeomS,
      hmono, hzero, hiso, d, hd, hmd, hq⟩ :=
    @exists_continuousFiltration_admissibleStrata l inferInstance K inferInstance hnorm
      hfinite X inferInstance _hdim _hl F hfree
  let U (k : Fin m) : X.ProEt := Scheme.ProEt.mk (V k.succ).ι
  let L (k : Fin m) :=
    (ContinuousFiltration.pull l K (t k)).obj
      ((ContinuousFiltration.pull l K (V k.succ).ι).obj F)
  have (k : Fin m) : IsNoetherian (S k) := (hgeomS k).1
  have hdimS (k : Fin m) : ∃ n : ℕ, topologicalKrullDim (S k) ≤ n := by
    obtain ⟨n, hn⟩ := _hdim
    exact ⟨n, (hgeomS k).2.1.trans hn⟩
  have (k : Fin m) : (L k).IsFiniteLocallyFree := (hgeomS k).2.2.2.2.2
  have hlattice (k : Fin m) := exists_constructible_integral_lattice l E (S k)
    (hdimS k) (hgeomS k).2.2.1 (L k)
  choose N hN α using hlattice
  have hp (k : Fin m) :
      IsContinuousConstructible X (latticeCoefficientIntegers l E)
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ∧
      IsCompletedModel l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ∧
      ∃ e : integralModelRationalize l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
          (piece (U k) (t k) K).obj (integralModelRationalize l E (S k) (N k)),
        IsNormalizedComparison l E (U k) (t k) (N k) e := by
    have : IsNoetherian (U k).left := (hgeomV k.succ).1
    have : IsOpenImmersion (U k).hom := inferInstanceAs (IsOpenImmersion (V k.succ).ι)
    have : QuasiCompact (U k).hom := (hgeomV k.succ).2.2.2.1
    have : QuasiSeparated (U k).hom := (hgeomV k.succ).2.2.2.2
    have : IsClosedImmersion (t k) := (ht k).1
    have hdimV : ∃ n : ℕ, topologicalKrullDim (U k).left ≤ n := by
      obtain ⟨n, hn⟩ := _hdim
      exact ⟨n, (hgeomV k.succ).2.1.trans hn⟩
    obtain ⟨_, hc, ⟨dc, ec, c, hnorm, hnat⟩, _⟩ :=
      integralPieceCompletionNormalization l E X _hdim _hl (U k) hdimV
        (hgeomV k.succ).2.2.1 (hdimS k) (hgeomS k).2.2.1 (t k)
        (TopologicalSpace.NoetherianSpace.isCompact _)
    exact ⟨(hc (N k) (hN k)).2.1, (hc (N k) (hN k)).2.2.2.2,
      c (N k) (hN k), (hnorm (N k) (hN k)).2.2.2.1⟩
  choose hconstruct hcomplete e he using hp
  refine ⟨m, fun k ↦ (ContinuousFiltration.piece K (V k)).obj F,
    fun k ↦ ContinuousFiltration.counit K (V k) F, d,
    hmono, hzero, hiso, hd, hmd, U, S, t, inferInstance, L, N, ?_, ?_,
    inferInstance, hN, hconstruct, hcomplete, fun k ↦ (α k).some, ?_, e, he,
    fun k ↦ e k ≪≫ (piece (U k) (t k) K).mapIso (α k).some, fun _ ↦ rfl⟩
  · intro k
    exact ⟨inferInstanceAs (IsOpenImmersion (V k.succ).ι),
      (hgeomV k.succ).2.2.2.1, (hgeomV k.succ).2.2.2.2,
      (ht k).1, (ht k).2.1⟩
  · intro k
    exact ⟨hdimS k, (hgeomS k).2.2.1⟩
  · intro k
    exact (hq k).some

end AlgebraicGeometry.ProEtale.RationalStratum
