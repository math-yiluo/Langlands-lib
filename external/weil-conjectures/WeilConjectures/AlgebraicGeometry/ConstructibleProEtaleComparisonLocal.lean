/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.ConstructibleSheaf.Pullback

/-! Constructible pro-etale comparison: locality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
private theorem stratified_local {X : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y), P f → P (g ≫ f))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ S : Scheme.Stratification U.toScheme,
      ∀ a : Fin S.n, P (S.immersion a ≫ U.ι))
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ S : Scheme.Stratification U.toScheme, ∀ a : Fin S.n, P (S.immersion a ≫ U.ι) := by
  classical
  let T := U.toScheme
  have : IsAffine T := hU
  have charts (x : T) : ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ S : Scheme.Stratification W.toScheme,
        ∀ a : Fin S.n, P (S.immersion a ≫ W.ι ≫ U.ι) := by
    obtain ⟨V, hxV, S, hS⟩ := h (U.ι x)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (X := T) (x := x) (U := U.ι ⁻¹ᵁ V) hxV
    let q := U.ι.resLE V W hWV
    let R := S.pullback q
    refine ⟨W, hW, hxW, R, ?_⟩
    intro a
    have hp := hP (S.immersion a ≫ V.ι) (pullback.fst (S.immersion a) q) (hS a)
    rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Hom.resLE_comp_ι] at hp
    exact hp
  choose W hW hxW S hS using charts
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : T ↦ (W x : Set T)) (fun x ↦ (W x).isOpen) (fun x _ ↦
      Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
  let w (a : Fin s.card) : T := (e a).1
  have coverW : (⋃ a : Fin s.card, (W (w a) : Set T)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, by simpa [w] using hxy⟩
  obtain ⟨R, hc, hR⟩ := Scheme.exists_global_stratification_factoring_local s.card
    (fun a ↦ W (w a)) (fun a ↦ hW (w a)) coverW
    (fun a ↦ S (w a)) (fun a b ↦ (S (w a)).isConstructible_stratum b)
  refine ⟨R, ?_⟩
  intro k
  obtain ⟨a, b, q, hq⟩ := hR k
  have hp := hP ((S (w a)).immersion b ≫ (W (w a)).ι ≫ U.ι) q (hS (w a) b)
  simpa only [← Category.assoc, hq] using hp

/-- Pointwise stratifications and the affine-local finite-presentation condition agree.
Source: blueprint constructible-comparison-local, Stacks Tags 09AJ and 09AK
(auxiliary; not a blueprint node).

Proof: in the forward direction choose an affine open neighborhood of the point
and forget finite presentation to finite generation. In the converse fix an affine
open U. Intersect each supplied point neighborhood with U, refine to an affine
open W, and pull back its stratification. Finite local models survive further
inverse image and its composition isomorphism. Quasi-compactness of U gives a
finite affine subcover. The global-stratification gluing lemma gives strata each
factoring through one of these local strata. Pull back the local models along
these factorizations. Finally Noetherianity upgrades their finite generation to
finite presentation. The empty cover and empty partition are included. -/
theorem constructibleComparison_local (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F ↔
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ S : Scheme.Stratification U.toScheme,
            (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
            ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
              (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
                (S.immersion a ≫ U.ι) A).obj
                  ((coefficientModelFixedScalars _ A).obj F)) := by
  intro F
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := ⊤) trivial
    obtain ⟨S, hc, hs⟩ := h U hU
    refine ⟨U, hxU, S, hc, ?_⟩
    intro a V
    obtain ⟨T, hT, ht⟩ := hs a V
    refine ⟨T, hT, ?_⟩
    intro W f hf
    obtain ⟨M, hM, e⟩ := ht W f hf
    have := hM
    exact ⟨M, inferInstance, e⟩
  · intro h U hU
    let E := (coefficientModelFixedScalars _ A).obj F
    let P {Y : Scheme.{u}} (f : Y ⟶ X) :=
      IsCoefficientModelLocallyConstantFinite
        (Scheme.coefficientProEtaleModelTopology.{u, v} Y) A
        ((Scheme.coefficientProEtaleFixedModulePullback f A).obj E)
    have hp : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y), P f → P (g ≫ f) := by
      intro Y Z f g hf
      exact coefficientProEtale_finite_comp g f A E hf
    have hh : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
        ∃ S : Scheme.Stratification V.toScheme, ∀ a : Fin S.n, P (S.immersion a ≫ V.ι) := by
      intro x
      obtain ⟨V, hx, S, hc, hs⟩ := h x
      exact ⟨V, hx, S, hs⟩
    obtain ⟨S, hs⟩ := stratified_local P hp hh U hU
    refine ⟨S, S.isConstructible_stratum, ?_⟩
    intro a V
    obtain ⟨T, hT, ht⟩ := hs a V
    refine ⟨T, hT, ?_⟩
    intro W f hf
    obtain ⟨M, hM, e⟩ := ht W f hf
    have := hM
    exact ⟨M, Module.finitePresentation_of_finite A M, e⟩

end AlgebraicGeometry.ProEtale
