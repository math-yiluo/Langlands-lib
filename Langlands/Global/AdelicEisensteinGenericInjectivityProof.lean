import Langlands.Global.AdelicEisensteinGenericInjectivityStatement
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicEisensteinTwistComparison
import Langlands.Global.EisensteinGenericInjectivity.Anchor
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicIntertwiningCocycleReduction
import Langlands.Global.AdelicRootHyperplaneReduction
import Langlands.Global.EisensteinGenericInjectivity.MeromorphicDet
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Generic injectivity of Eisenstein series (proof)

Bernstein–Lapid, formula (8.4). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct Matrix Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Global.EisensteinGenericInjectivity

/-- **Generic injectivity of Eisenstein series** (Bernstein–Lapid (8.4)). -/
theorem eisensteinGenericInjectivity : EisensteinGenericInjectivityStatement.{u} := by
  intro F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc hKmax
    hrho Idx _ φ hφ E D hE hagree n e
  classical
  have : Smooth G.X.hom := hG.smooth
  by_cases hI : IsEmpty Idx
  · exact ⟨univ, isOpen_univ, dense_univ, fun s _ _ c _ g => by simp⟩
  rw [not_isEmpty_iff] at hI
  obtain ⟨i₀⟩ := hI
  let D' : Set (Fin n → ℂ) := e ⁻¹' D
  have hmer : ∀ i g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => E i (e s) g) D' :=
    fun i g => (hE i g).2 n e
  have hD'o : IsOpen D' := (hmer i₀ 1).1
  have hD'd : Dense D' := (hmer i₀ 1).2.1
  -- a basis subfamily of the forms
  obtain ⟨m, ψ, b, hb, hψind, hrel⟩ : ∃ (m : ℕ) (ψ : Fin m → AdelicGroupPoints F G → ℂ)
      (b : Fin m → Idx), (∀ k, φ (b k) = ψ k) ∧ LinearIndependent ℂ ψ ∧
        ∀ i, ∃ c : Fin m → ℂ, ∑ k, c k • ψ k = φ i := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (range φ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range φ)
    obtain ⟨ψ, hψmem, hψspan, hψind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (range φ)
    choose b hb using hψmem
    refine ⟨_, ψ, b, hb, hψind, fun i => ?_⟩
    have h : φ i ∈ Submodule.span ℂ (range ψ) := by
      rw [hψspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  choose co hco using hrel
  -- a common regularity threshold
  choose Rc hRc using fun i => eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hU K
    hK rho hsmooth hcalc (φ i) hKmax hrho (hφ i)
  choose Ra hRa using hagree
  let R : ℝ := ∑ i, (|Rc i| + |Ra i|)
  have hle : ∀ i, Rc i ≤ R ∧ Ra i ≤ R := by
    intro i
    have hi : |Rc i| + |Ra i| ≤ R :=
      Finset.single_le_sum (f := fun i => |Rc i| + |Ra i|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    exact ⟨(le_abs_self _).trans (le_of_add_le_of_nonneg_left hi (abs_nonneg _)),
      (le_abs_self _).trans (le_of_add_le_of_nonneg_right hi (abs_nonneg _))⟩
  let Reg : Set (Fin n → ℂ) := {s | r.IsRegularParameter hA hT R (e s)}
  have hRego : IsOpen Reg := isOpen_setOf_isRegularParameter r hA hT hG R e
  have hRegne : Reg.Nonempty := by
    obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT R
    exact ⟨e.symm lam, by simpa only [Reg, mem_ofPred_eq, LinearEquiv.apply_symm_apply] using hlam⟩
  have hagr : ∀ i, ∀ s ∈ Reg, E i (e s) = hK.eisensteinSeries (φ i) (e s) :=
    fun i s hs => hRa i _ (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hle i).2 hs)
  have hsumm : ∀ i (g : AdelicGroupPoints F G), ∀ s ∈ Reg,
      Summable fun c => hK.eisensteinTerm (φ i) (e s) g c := by
    intro i g s hs
    obtain ⟨bd, hbd, hbound⟩ := hRc i {g} isCompact_singleton n e {s} isCompact_singleton
      (by simpa using ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hle i).1 hs)
    exact Summable.of_norm_bounded hbd fun c => hbound c g rfl s rfl
  -- the continued series satisfy the linear relations of the forms
  have hErel : ∀ i (g : AdelicGroupPoints F G), ∀ s ∈ D',
      E i (e s) g = ∑ k, co i k * E (b k) (e s) g := by
    intro i g
    have hg : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => ∑ k, co i k * E (b k) (e s) g) D' := by
      have h := IsMeromorphicOn.sum (Finset.univ : Finset (Fin m)) hD'o hD'd
        (a := fun k s => co i k * E (b k) (e s) g)
        (fun k _ => by
          convert (hmer (b k) g).mul_const (co i k) using 1
          funext s
          exact mul_comm _ _)
      convert h using 1
      funext s
      simp only [Finset.sum_apply]
    have heq : EqOn (fun s => E i (e s) g) (fun s => ∑ k, co i k * E (b k) (e s) g)
        (Reg ∩ (D' ∩ D')) := by
      rintro s ⟨hs, -⟩
      simp only
      rw [hagr i s hs, ← hco i,
        hK.eisensteinSeries_eq_finset_sum_of_twist hK Finset.univ (co i) _ ψ (e s)
          (fun x => by simp only [IsIwasawaCompact.parameterTwist, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]) g
          fun k _ => by rw [← hb k]; exact hsumm (b k) g s hs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hagr (b k) s hs, hb k]
    intro s hs
    exact (hmer i g).eqOn_of_eqOn_open hg hRego hRegne heq ⟨hs, hs⟩
  -- an anchor point in the regular region
  have hcont : ∀ k, Continuous (ψ k) := fun k => hb k ▸ (hφ (b k)).2.1.1
  have hinv : ∀ k, IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (ψ k) :=
    fun k => hb k ▸ (hφ (b k)).1
  have hconv : ∀ k, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∀ (n' : ℕ) (e' : (Fin n' → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (Λ : Set (Fin n' → ℂ)), IsCompact Λ →
        (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e' s)) →
        ∃ bd : ParabolicRationalCosets F p → ℝ, Summable bd ∧
          ∀ c, ∀ g ∈ C, ∀ s ∈ Λ, ‖hK.eisensteinTerm (ψ k) (e' s) g c‖ ≤ bd c := by
    intro k C hC n' e' Λ hΛ hreg
    rw [← hb k]
    exact hRc (b k) C hC n' e' Λ hΛ fun s hs =>
      ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hle (b k)).1 (hreg s hs)
  obtain ⟨s₁, hs₁, g, hdet⟩ := exists_regular_det_ne_zero r hA hT hG hU hK ψ hcont
    hinv hψind R hconv e (hRego.inter hD'o) (hD'd.inter_open_nonempty Reg hRego hRegne)
    fun s hs => hs.1
  -- the determinant of the continued series
  let detE : (Fin n → ℂ) → ℂ := fun s => (Matrix.of fun i k => E (b k) (e s) (g i)).det
  have hdetE : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) detE D' :=
    isMeromorphicOn_det (fun i k s => E (b k) (e s) (g i)) hD'o hD'd fun i k => hmer (b k) (g i)
  have hdetE₁ : detE s₁ ≠ 0 := by
    have h : detE s₁ = (Matrix.of fun i k => hK.eisensteinSeries (ψ k) (e s₁) (g i)).det := by
      simp only [detE]
      congr 1
      ext i k
      simp only [Matrix.of_apply]
      rw [hagr (b k) s₁ hs₁.1, hb k]
    rw [h]
    exact hdet
  let O : Set (Fin n → ℂ) := D' ∩ detE ⁻¹' {0}ᶜ
  have hOo : IsOpen O :=
    ((isHolomorphicOn_iff_differentiableOn_scalar.mp hdetE.2.2.1).continuousOn).isOpen_inter_preimage
      hD'o isOpen_compl_singleton
  have hOd : Dense O := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hzero : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun _ => (0 : ℂ)) D' :=
      (isMeromorphicOn_const 0).restrict_domain hD'o hD'd (subset_univ _)
    have heq : EqOn detE (fun _ => (0 : ℂ)) (V ∩ (D' ∩ D')) := by
      rintro s ⟨hsV, hsD, -⟩
      by_contra hne
      have hmem : s ∈ V ∩ O := ⟨hsV, hsD, hne⟩
      rw [hempty] at hmem
      exact hmem
    exact hdetE₁ (hdetE.eqOn_of_eqOn_open hzero hV hVne heq ⟨hs₁.2, hs₁.2⟩)
  refine ⟨O, hOo, hOd, fun s hs _ c hc g' => ?_⟩
  let dv : Fin m → ℂ := fun k => ∑ i, c i * co i k
  have hcomb : ∀ g'', ∑ k, dv k * E (b k) (e s) g'' = 0 := by
    intro g''
    have h := hc g''
    rw [Finset.sum_congr rfl fun i _ => by rw [hErel i g'' s hs.1]] at h
    simp only [Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    simpa only [dv, Finset.sum_mul, mul_assoc] using h
  have hmul : (Matrix.of fun i k => E (b k) (e s) (g i)) *ᵥ dv = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    simpa only [mul_comm] using hcomb (g i)
  have hdv : dv = 0 := Matrix.eq_zero_of_mulVec_eq_zero hs.2 hmul
  calc ∑ i, c i * φ i g' = ∑ i, c i * ∑ k, co i k * ψ k g' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hco i]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ k, dv k * ψ k g' := by
        simp only [dv, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by simp [hdv]

end Langlands.Global
