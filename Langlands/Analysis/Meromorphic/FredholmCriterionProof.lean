import Langlands.Analysis.Meromorphic.FredholmCriterionStatement
import Langlands.Analysis.Meromorphic.RieszFredholm
import Langlands.Analysis.Meromorphic.WeakHolomorphy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! # Proof of Fredholm's criterion for local finite type

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §3.4: the Lemma
(Fredholm's criterion) and Corollary 3.4. -/

noncomputable section
set_option autoImplicit false

universe uE uM uB uC

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology
open scoped Manifold

namespace FredholmCriterion

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

omit [CompleteSpace B] in
/-- A finite-dimensional subspace of `B` is the range of an injective operator `ℂⁿ → B`. -/
theorem exists_injective_range_eq (W : Submodule ℂ B) [FiniteDimensional ℂ W] :
    ∃ (n : ℕ) (ι : (Fin n → ℂ) →L[ℂ] B), Function.Injective ι ∧ ∀ x ∈ W, ∃ c, ι c = x := by
  let b := Module.finBasis ℂ W
  let f : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] B := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  refine ⟨Module.finrank ℂ W, LinearMap.toContinuousLinearMap f, ?_, ?_⟩
  · intro c c' h
    have h' : (b.equivFun.symm c : B) = b.equivFun.symm c' := h
    exact b.equivFun.symm.injective (Subtype.ext h')
  · intro x hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    simp [f]

/-- Fredholm's criterion in a chart: for a weakly holomorphic family `μ z` on an open set `T`
of a finite-dimensional complex space, left invertible modulo compact operators at `z₀`, the
kernels of `μ z` are contained in the ranges of an injective weakly holomorphic family
`ℓ z : ℂⁿ → B` on an open neighbourhood `T' ⊆ T` of `z₀`. -/
theorem exists_finiteType_euclidean {μ : E → B →L[ℂ] C} {T : Set E} (hT : IsOpen T)
    (hμ : ∀ v (φ : StrongDual ℂ C), DifferentiableOn ℂ (fun z => φ (μ z v)) T)
    {z₀ : E} (hz₀ : z₀ ∈ T) (D : C →L[ℂ] B)
    (hD : IsCompactOperator (D ∘L μ z₀ - ContinuousLinearMap.id ℂ B)) :
    ∃ T' ⊆ T, IsOpen T' ∧ z₀ ∈ T' ∧ ∃ (n : ℕ) (ℓ : E → (Fin n → ℂ) →L[ℂ] B),
      (∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun z => φ (ℓ z v)) T') ∧
      (∀ z ∈ T', Function.Injective (ℓ z)) ∧
      ∀ z ∈ T', ∀ v, μ z v = 0 → v ∈ Set.range (ℓ z) := by
  obtain ⟨G, F, hF, hGF⟩ := RieszFredholm.exists_leftInverse_mod_finiteRank (μ z₀) D hD
  set X : E → B →L[ℂ] B := fun z => 1 + G ∘L (μ z - μ z₀) with hXdef
  have hX : ∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun z => φ (X z v)) T := by
    intro v φ
    have h := ((hμ v (φ ∘L G)).sub
      (differentiableOn_const ((φ ∘L G) (μ z₀ v)))).const_add (φ v)
    refine h.congr fun z _ => ?_
    simp [hXdef, map_sub]
  have hXc : ContinuousOn X T := fun z hz =>
    (WeakHolomorphy.continuousAt_of_weak hT hX hz).continuousWithinAt
  have hT'o : IsOpen (T ∩ X ⁻¹' {x | IsUnit x}) := hXc.isOpen_inter_preimage hT Units.isOpen
  have hz₀' : z₀ ∈ T ∩ X ⁻¹' {x | IsUnit x} := ⟨hz₀, by simp [hXdef]⟩
  have hunit : ∀ z ∈ T ∩ X ⁻¹' {x | IsUnit x}, IsUnit (X z) := fun z hz => hz.2
  have hinv : ∀ z ∈ T ∩ X ⁻¹' {x | IsUnit x}, ∀ t, Ring.inverse (X z) (X z t) = t := by
    intro z hz t
    obtain ⟨u, hu⟩ := hunit z hz
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  have hinv' : ∀ z ∈ T ∩ X ⁻¹' {x | IsUnit x}, ∀ t, X z (Ring.inverse (X z) t) = t := by
    intro z hz t
    obtain ⟨u, hu⟩ := hunit z hz
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
  have : FiniteDimensional ℂ (LinearMap.range (F : B →ₗ[ℂ] B)) := hF
  obtain ⟨n, ι, hι, hιW⟩ := exists_injective_range_eq (LinearMap.range (F : B →ₗ[ℂ] B))
  refine ⟨T ∩ X ⁻¹' {x | IsUnit x}, inter_subset_left, hT'o, hz₀', n,
    fun z => Ring.inverse (X z) ∘L ι, ?_, ?_, ?_⟩
  · intro c φ
    exact WeakHolomorphy.differentiableOn_inverse_apply hT'o
      (fun v φ => (hX v φ).mono inter_subset_left) hunit (ι c) φ
  · intro z hz
    have hinj : Function.Injective ⇑(Ring.inverse (X z) : B →L[ℂ] B) := fun a b h => by
      rw [← hinv' z hz a, ← hinv' z hz b, h]
    exact hinj.comp hι
  · intro z hz v hv
    have h1 : G (μ z₀ v) = v - F v := by
      simpa using congrArg (fun A : B →L[ℂ] B => A v) hGF
    have hXv : X z v = F v := by
      simp [hXdef, hv, h1]
    obtain ⟨c, hc⟩ := hιW (F v) (LinearMap.mem_range_self _ v)
    refine ⟨c, ?_⟩
    change Ring.inverse (X z) (ι c) = v
    rw [hc, ← hXv, hinv z hz]

end Euclidean

end FredholmCriterion

open FredholmCriterion in
/-- **Fredholm's criterion** (Bernstein–Lapid §3.4, Lemma). -/
theorem fredholmCriterion : FredholmCriterionStatement.{uE, uM, uB, uC} := by
  intro E _ _ _ M _ _ _ B _ _ _ C _ _ _ μ s₀ hμ hD
  obtain ⟨D, hD⟩ := hD
  set e := extChartAt 𝓘(ℂ, E) s₀ with he
  have hμ' : ∀ v (φ : StrongDual ℂ C),
      DifferentiableOn ℂ (fun z => φ (μ (e.symm z) v)) e.target := by
    intro v φ
    have h := (hμ v φ).comp (mdifferentiableOn_extChartAt_symm (I := 𝓘(ℂ, E)) (x := s₀))
      (mapsTo_univ _ _)
    exact h.differentiableOn
  have hz₀ : e s₀ ∈ e.target := mem_extChartAt_target s₀
  have hD' : IsCompactOperator (D ∘L μ (e.symm (e s₀)) - ContinuousLinearMap.id ℂ B) := by
    rwa [he, extChartAt_to_inv]
  obtain ⟨T', -, hT'o, hz₀', n, ℓ, hℓ, hinj, hran⟩ :=
    exists_finiteType_euclidean (isOpen_extChartAt_target s₀) hμ' hz₀ D hD'
  refine ⟨e.source ∩ e ⁻¹' T', isOpen_extChartAt_preimage' s₀ hT'o,
    ⟨mem_extChartAt_source s₀, hz₀'⟩, n, fun s => ℓ (e s), ?_, ?_, ?_⟩
  · intro v φ
    have h1 : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun z => φ (ℓ z v)) T' :=
      (hℓ v φ).mdifferentiableOn
    have h2 : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, E) e e.source := by
      rw [he, extChartAt_source]
      exact mdifferentiableOn_extChartAt
    exact h1.comp (h2.mono inter_subset_left) (fun s hs => hs.2)
  · intro s hs
    exact hinj _ hs.2
  · intro s hs v hv
    have hv' : μ (e.symm (e s)) v = 0 := by rwa [e.left_inv hs.1]
    exact hran _ hs.2 v hv'

/-- **Corollary 3.4** of Bernstein–Lapid: the Hilbert-space form of Fredholm's criterion. -/
theorem hilbertFredholmCriterion : HilbertFredholmCriterionStatement.{uE, uM, uB, uC} := by
  intro E _ _ _ M _ _ _ B _ _ _ C _ _ _ μ ν s₀ hμ hν hemb hcpt
  obtain ⟨K, hK⟩ := (μ s₀).antilipschitz_of_isEmbedding hemb
  have hclosed : IsClosed (Set.range (μ s₀)) :=
    hK.isClosed_range (μ s₀).uniformContinuous
  have hcc : (μ s₀).range.ClosedComplemented := by
    have : CompleteSpace (μ s₀).range := hclosed.completeSpace_coe
    exact (μ s₀).range.isTopCompl_orthogonal.closedComplemented
  have hL : (μ s₀).HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range
      hemb.injective hclosed hcc
  set L := hL.leftInverse with hLdef
  have hLμ : L ∘L μ s₀ = ContinuousLinearMap.id ℂ B := by
    ext x
    exact hL.leftInverse_leftInverse x
  have hD : IsCompactOperator (L ∘L (μ - ν) s₀ - ContinuousLinearMap.id ℂ B) := by
    have h : L ∘L (μ - ν) s₀ - ContinuousLinearMap.id ℂ B = -(L ∘L ν s₀) := by
      rw [Pi.sub_apply, ContinuousLinearMap.comp_sub, hLμ]
      abel
    rw [h]
    exact (hcpt.clm_comp L).neg
  have hμν : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) (μ - ν) Set.univ := by
    intro v φ
    have h := (hμ v φ).sub (hν v φ)
    refine h.congr fun s _ => ?_
    simp
  obtain ⟨U, hUo, hsU, n, ℓ, hℓ, hinj, hran⟩ :=
    fredholmCriterion (μ - ν) s₀ hμν ⟨L, hD⟩
  refine ⟨U, hUo, hsU, n, ℓ, hℓ, hinj, fun s hs v hv => hran s hs ?_⟩
  simpa [sub_eq_zero] using hv

/-- The Lemma (Fredholm's criterion) and Corollary 3.4 of Bernstein–Lapid. -/
theorem fredholmFiniteType : FredholmFiniteTypeStatement.{uE, uM, uB, uC} :=
  ⟨fredholmCriterion, hilbertFredholmCriterion⟩

end Langlands.Analysis.Meromorphic
