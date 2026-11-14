import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Invariant complements for representations of compact groups

Let `K` be a compact Hausdorff topological group and `ρ` a representation of `K` on a
finite-dimensional complex normed space `E`, continuous in the sense that every orbit map
`k ↦ ρ k y` is continuous. Every `K`-stable subspace `U` then has a `K`-stable complement
(`exists_isCompl_invariant`). The proof averages a linear projection onto `U` over the
normalized Haar measure: `P y = ∫ ρ k (p₀ (ρ k⁻¹ y)) dk` is a `K`-equivariant projection onto
`U`, and its kernel is the complement.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace Langlands.CompactMaschke

variable {K : Type*} [Group K] [TopologicalSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Joint continuity of a representation with continuous orbit maps on a finite-dimensional
space. -/
theorem continuous_apply_of_continuous (ρ : Representation ℂ K E)
    (hρ : ∀ y, Continuous fun k => ρ k y) {X : Type*} [TopologicalSpace X] {g : X → K}
    {z : X → E} (hg : Continuous g) (hz : Continuous z) :
    Continuous fun x => ρ (g x) (z x) := by
  classical
  let b := Module.finBasis ℂ E
  have h : ∀ x, ρ (g x) (z x) = ∑ j, b.coord j (z x) • ρ (g x) (b j) := fun x => by
    conv_lhs => rw [← b.sum_repr (z x)]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  simp_rw [h]
  exact continuous_finsetSum _ fun j _ =>
    ((LinearMap.continuous_of_finiteDimensional (b.coord j)).comp hz).smul
      ((hρ (b j)).comp hg)

variable [IsTopologicalGroup K] [CompactSpace K]

/-- **Maschke's theorem for compact groups.** A `K`-stable subspace of a finite-dimensional
continuous representation of a compact group has a `K`-stable complement. -/
theorem exists_isCompl_invariant (ρ : Representation ℂ K E)
    (hρ : ∀ y, Continuous fun k => ρ k y) (U : Submodule ℂ E)
    (hU : ∀ (k : K), ∀ u ∈ U, ρ k u ∈ U) :
    ∃ U' : Submodule ℂ E, IsCompl U U' ∧ ∀ (k : K), ∀ x ∈ U', ρ k x ∈ U' := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts K := ⊤
  let μ : Measure K := Measure.haarMeasure K₀
  have : IsProbabilityMeasure μ := ⟨by
    have h := Measure.haarMeasure_self (K₀ := K₀)
    rwa [show ((K₀ : Set K)) = Set.univ from rfl] at h⟩
  have hρinv : ∀ (k : K) (y : E), ρ k (ρ k⁻¹ y) = y := fun k y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨C, hC⟩ := U.exists_isCompl
  let p₀ : E →ₗ[ℂ] E := U.subtype ∘ₗ U.projectionOnto C hC
  have hp₀U : ∀ x, p₀ x ∈ U := fun x => (U.projectionOnto C hC x).2
  have hp₀id : ∀ u ∈ U, p₀ u = u := fun u hu => by
    change ((U.projectionOnto C hC u : U) : E) = u
    rw [Submodule.projectionOnto_apply_left hC ⟨u, hu⟩]
  let φ : E → K → E := fun y k => ρ k (p₀ (ρ k⁻¹ y))
  have hφc : ∀ y, Continuous (φ y) := fun y =>
    continuous_apply_of_continuous ρ hρ continuous_id
      ((LinearMap.continuous_of_finiteDimensional p₀).comp
        (continuous_apply_of_continuous ρ hρ continuous_inv continuous_const))
  have hφi : ∀ y, Integrable (φ y) μ := fun y =>
    (hφc y).integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hφU : ∀ y k, φ y k ∈ U := fun y k => hU k _ (hp₀U _)
  let P : E →ₗ[ℂ] E :=
    { toFun := fun y => ∫ k, φ y k ∂μ
      map_add' := fun y z => by
        rw [← integral_add (hφi y) (hφi z)]
        congr 1
        funext k
        simp only [φ, map_add]
      map_smul' := fun c y => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1
        funext k
        simp only [φ, map_smul] }
  have hPapply : ∀ y, P y = ∫ k, φ y k ∂μ := fun y => rfl
  -- `P` takes values in `U`
  have hPU : ∀ y, P y ∈ U := fun y => by
    let L : E →L[ℂ] E := (LinearMap.id - p₀).toContinuousLinearMap
    have hL : ∀ z, z ∈ U → L z = 0 := fun z hz => by
      change z - p₀ z = 0
      rw [hp₀id z hz, sub_self]
    have h0 : L (P y) = 0 := by
      rw [hPapply, ← ContinuousLinearMap.integral_comp_comm L (hφi y)]
      simp only [hL _ (hφU y _), integral_zero]
    have h1 : P y - p₀ (P y) = 0 := h0
    rw [sub_eq_zero] at h1
    rw [h1]
    exact hp₀U _
  -- `P` fixes `U`
  have hPid : ∀ u ∈ U, P u = u := fun u hu => by
    have hφu : ∀ k, φ u k = u := fun k => by
      change ρ k (p₀ (ρ k⁻¹ u)) = u
      rw [hp₀id _ (hU _ u hu), hρinv]
    rw [hPapply]
    simp only [hφu, integral_const, probReal_univ, one_smul]
  -- `P` is equivariant
  have hPeq : ∀ (g : K) (y : E), P (ρ g y) = ρ g (P y) := fun g y => by
    have hshift : ∀ k, φ (ρ g y) (g * k) = ρ g (φ y k) := fun k => by
      change ρ (g * k) (p₀ (ρ (g * k)⁻¹ (ρ g y))) = ρ g (ρ k (p₀ (ρ k⁻¹ y)))
      rw [mul_inv_rev, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    rw [hPapply, hPapply, ← integral_mul_left_eq_self (μ := μ) (φ (ρ g y)) g]
    simp only [hshift]
    exact ContinuousLinearMap.integral_comp_comm (ρ g).toContinuousLinearMap (hφi y)
  refine ⟨LinearMap.ker P, ?_, fun k x hx => ?_⟩
  · have h := LinearMap.isCompl_of_proj (f := P.codRestrict U hPU)
      (fun x => Subtype.ext (hPid x x.2))
    rwa [LinearMap.ker_codRestrict] at h
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [hPeq, hx, map_zero]

/-- **Maschke's theorem for weakly continuous representations.** The same statement for a
finite-dimensional complex vector space without a norm, assuming only that every linear form
of every orbit map is continuous. -/
theorem exists_isCompl_invariant_of_weak {F : Type*} [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ F] (ρ : Representation ℂ K F)
    (hρ : ∀ (μ : F →ₗ[ℂ] ℂ) (y : F), Continuous fun k => μ (ρ k y)) (U : Submodule ℂ F)
    (hU : ∀ (k : K), ∀ u ∈ U, ρ k u ∈ U) :
    ∃ U' : Submodule ℂ F, IsCompl U U' ∧ ∀ (k : K), ∀ x ∈ U', ρ k x ∈ U' := by
  classical
  let b := Module.finBasis ℂ F
  let : NormedAddCommGroup F :=
    NormedAddCommGroup.induced F (Fin (Module.finrank ℂ F) → ℂ) b.equivFun b.equivFun.injective
  let : NormedSpace ℂ F := NormedSpace.induced ℂ F (Fin (Module.finrank ℂ F) → ℂ) b.equivFun
  refine exists_isCompl_invariant ρ (fun y => ?_) U hU
  have hc : Continuous fun k => b.equivFun (ρ k y) :=
    continuous_pi fun j => by simpa using hρ (b.coord j) y
  exact continuous_induced_rng.mpr hc

section Lifting

variable {N : Type*} [AddCommGroup N] [Module ℂ N] {N'' : Type*} [AddCommGroup N'']
  [Module ℂ N'']

/-- **Lifting intertwiners.** Let `κ` be a representation of the compact group `K` on `N`
whose vectors lie in finite-dimensional stable subspaces and whose orbit maps are weakly
continuous, and let `q : N → N''` be equivariant. Every intertwiner `ψ` from a matrix
representation `τ` into `N''` with values in the range of `q` lifts through `q`. -/
theorem exists_lift_intertwiner (κ : Representation ℂ K N) (κ'' : Representation ℂ K N'')
    (hfin : ∀ x : N, ∃ E : Submodule ℂ N, FiniteDimensional ℂ E ∧ x ∈ E ∧
      ∀ (k : K), ∀ y ∈ E, κ k y ∈ E)
    (hweak : ∀ (μ : N →ₗ[ℂ] ℂ) (x : N), Continuous fun k => μ (κ k x))
    (q : N →ₗ[ℂ] N'') (hq : ∀ k x, q (κ k x) = κ'' k (q x)) {d : ℕ}
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) (ψ : (Fin d → ℂ) →ₗ[ℂ] N'')
    (hψ : ∀ k x, ψ (τ k *ᵥ x) = κ'' k (ψ x)) (hψq : ∀ x, ψ x ∈ LinearMap.range q) :
    ∃ ψ' : (Fin d → ℂ) →ₗ[ℂ] N, (∀ k x, ψ' (τ k *ᵥ x) = κ k (ψ' x)) ∧ q ∘ₗ ψ' = ψ := by
  classical
  -- a finite-dimensional stable subspace containing lifts of the values on a basis
  choose n hn using fun i : Fin d => hψq (Pi.single i 1)
  choose E hEf hnE hEs using fun i : Fin d => hfin (n i)
  let E' : Submodule ℂ N := ⨆ i, E i
  have : FiniteDimensional ℂ E' := Submodule.finiteDimensional_iSup _
  have hE's : ∀ (k : K), ∀ y ∈ E', κ k y ∈ E' := by
    intro k y hy
    refine Submodule.iSup_induction E (motive := fun y => κ k y ∈ E') hy (fun i y hy => ?_) ?_ ?_
    · exact Submodule.mem_iSup_of_mem i (hEs i k y hy)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  have hnE' : ∀ i, n i ∈ E' := fun i => Submodule.mem_iSup_of_mem i (hnE i)
  -- the restricted representation on `E'`
  let σ : Subrepresentation κ := ⟨E', fun k y hy => hE's k y hy⟩
  let ρ : Representation ℂ K E' := σ.toRepresentation
  have hρ : ∀ k (y : E'), ((ρ k y : E') : N) = κ k y := fun k y => rfl
  have hρw : ∀ (μ : E' →ₗ[ℂ] ℂ) (y : E'), Continuous fun k => μ (ρ k y) := by
    intro μ y
    obtain ⟨g, hg⟩ := LinearMap.exists_extend μ
    have : ∀ k, μ (ρ k y) = g (κ k y) := fun k => by
      rw [← hρ, ← hg]
      rfl
    simp_rw [this]
    exact hweak g y
  -- `q` on `E'`, its kernel and a stable complement
  let qE : E' →ₗ[ℂ] N'' := q ∘ₗ E'.subtype
  have hqE : ∀ k (y : E'), qE (ρ k y) = κ'' k (qE y) := fun k y => hq k y
  obtain ⟨U', hU', hU's⟩ := exists_isCompl_invariant_of_weak ρ hρw (LinearMap.ker qE)
    (fun k u hu => by rw [LinearMap.mem_ker, hqE, LinearMap.mem_ker.mp hu, map_zero])
  have hinj : Function.Injective (qE ∘ₗ U'.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have h1 : (x : E') ∈ LinearMap.ker qE := hx
    have h2 : (x : E') ∈ LinearMap.ker qE ⊓ U' := ⟨h1, x.2⟩
    rw [hU'.inf_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : ∀ x, ψ x ∈ LinearMap.range (qE ∘ₗ U'.subtype) := by
    have hrq : LinearMap.range qE ≤ LinearMap.range (qE ∘ₗ U'.subtype) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ LinearMap.ker qE ⊔ U' := by rw [hU'.sup_eq_top]; trivial
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨c, hc⟩, ?_⟩
      simp [LinearMap.mem_ker.mp ha]
    intro x
    apply hrq
    have hx : x = ∑ i, x i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ⟨⟨n i, hnE' i⟩, ?_⟩
    exact hn i
  let e := LinearEquiv.ofInjective (qE ∘ₗ U'.subtype) hinj
  let ψ' : (Fin d → ℂ) →ₗ[ℂ] N :=
    E'.subtype ∘ₗ U'.subtype ∘ₗ e.symm.toLinearMap ∘ₗ ψ.codRestrict _ hrange
  have hψ'U : ∀ x, ∃ u : U', ψ' x = ((u : E') : N) := fun x => ⟨_, rfl⟩
  have hqψ' : ∀ x, q (ψ' x) = ψ x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ x, hrange x⟩)
  refine ⟨ψ', fun k x => ?_, LinearMap.ext hqψ'⟩
  -- equivariance: both sides lie in the stable complement, where `q` is injective
  obtain ⟨u₁, hu₁⟩ := hψ'U (τ k *ᵥ x)
  obtain ⟨u₂, hu₂⟩ := hψ'U x
  let w : U' := ⟨ρ k u₂, hU's k _ u₂.2⟩
  have hw : ((w : E') : N) = κ k (ψ' x) := by rw [hu₂]; rfl
  have hq0 : (qE ∘ₗ U'.subtype) (u₁ - w) = 0 := by
    rw [map_sub]
    change q ((u₁ : E') : N) - q ((w : E') : N) = 0
    rw [← hu₁, hw, hq, hqψ', hqψ', hψ, sub_self]
  have := hinj (hq0.trans (map_zero _).symm)
  rw [sub_eq_zero] at this
  rw [hu₁, this, hw]

end Lifting

end Langlands.CompactMaschke
