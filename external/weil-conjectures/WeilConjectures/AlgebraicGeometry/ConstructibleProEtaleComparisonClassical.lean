/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedContinuity
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation

/-! Constructible pro-etale comparison: classicality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- An affine-locally constructible module has invertible continuity maps on a qcqs scheme.
Source: blueprint constructible-comparison-classical, Stacks Tags 09AJ and 09AK
(auxiliary; not a blueprint node).

Proof: choose an affine neighborhood of each point and its constructibility
stratification, regarding every finite-presentation model as a finite model.
Quasi-compactness gives a finite subcover. The qcqs gluing lemma constructs one
global finite stratification, together with factorizations of its immersions
through the local strata. The inverse-image composition isomorphism and stability
of finite local systems under inverse image provide models on its strata. Apply
the single-stratification continuity lemma to this global partition. -/
theorem constructibleComparison_classical (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ [CompactSpace X] [QuasiSeparatedSpace X],
      ∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F →
          ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
            (P : AffinePresentation X I),
            IsIso (continuityMap P
              ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
                ((coefficientModelFixedScalars _ A).obj F).obj)) := by
  classical
  intro _ _ F hF I _ _ P
  have charts (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ S : Scheme.Stratification U.toScheme,
        ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
          (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
          ((Scheme.coefficientProEtaleFixedModulePullback (S.immersion a ≫ U.ι) A).obj
            ((coefficientModelFixedScalars _ A).obj F)) := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := ⊤) trivial
    obtain ⟨S, hc, hs⟩ := hF U hU
    refine ⟨U, hU, hxU, S, ?_⟩
    intro a V
    obtain ⟨T, hT, ht⟩ := hs a V
    refine ⟨T, hT, ?_⟩
    intro W f hf
    obtain ⟨M, hM, e⟩ := ht W f hf
    have := hM
    exact ⟨M, inferInstance, e⟩
  choose U hU hxU S hS using charts
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (fun x _ ↦
      Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
  let w (a : Fin s.card) : X := (e a).1
  have coverU : (⋃ a : Fin s.card, (U (w a) : Set X)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, by simpa [w] using hxy⟩
  obtain ⟨R, hc, hR⟩ := Scheme.exists_global_stratification_factoring_local s.card
    (fun a ↦ U (w a)) (fun a ↦ hU (w a)) coverU
    (fun a ↦ S (w a)) (fun a b ↦ (S (w a)).isConstructible_stratum b)
  apply coefficientStratified_continuity X A F R _ P
  intro k
  obtain ⟨a, b, q, hq⟩ := hR k
  have h := coefficientProEtale_finite_comp q
    ((S (w a)).immersion b ≫ (U (w a)).ι) A
    ((coefficientModelFixedScalars _ A).obj F) (hS (w a) b)
  rwa [hq] at h

end AlgebraicGeometry.ProEtale
