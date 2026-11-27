import Langlands.Analysis.CompactFunctionalFactorization
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity
import Langlands.Geometry.Manifold.LinearLieGroup.Realization

/-! # Smooth kernels from compactly bounded functionals on a solution space -/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace Metric
open scoped Manifold ContDiff Topology Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Analysis.CompactFunctional

open Langlands.LinearLieGroup
open DixmierMalliavin (contDiff_cons_kernel tsupport_cons_kernel)

variable {H : Type*} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

/-- A bounded functional evaluated on the restriction to its compact domain. -/
private structure LocalFunctional (H : Type*) [TopologicalSpace H] where
  domain : Compacts H
  weight : C(domain, ℂ) →L[ℂ] ℂ

private def coefficient (L : LocalFunctional H) (f : C(H, ℂ)) (a : H) : ℂ :=
  L.weight (restrict L.domain (shift a f))

private theorem continuous_coefficient (L : LocalFunctional H) (f : C(H, ℂ)) :
    Continuous (coefficient L f) := by
  apply L.weight.continuous.comp
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))

section Product

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {G : Subgroup Aˣ} {𝔤 : Submodule ℝ A} (h : IsExpLieAlgebra G 𝔤) (e : H ≃ₜ* G)

private def inverseCoefficient (L : LocalFunctional H) (f : C(H, ℂ)) (x : G) : ℂ :=
  coefficient L f ((e.symm x)⁻¹)

omit [FiniteDimensional ℝ A] in
private theorem inverseCoefficient_factor_direction (S : Submodule ℂ C(H, ℂ))
    (hshift : ∀ a f, f ∈ S → shift a f ∈ S) (L : LocalFunctional H) (X : 𝔤)
    {ε : ℝ} (hε : 0 < ε)
    (hsmooth : ∀ f ∈ S, ContDiff ℝ ∞
      (fun s : ℝ => restrict L.domain (shift (e.symm (h.expG (s • (-X)))) f)))
    (hbound : LineDerivativeBounds S L.domain (fun s : ℝ => e.symm (h.expG (s • (-X)))) ε) :
    ∃ (M : LocalFunctional H) (a b : ℝ → ℂ), ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      tsupport a ⊆ Icc (-ε) ε ∧ tsupport b ⊆ Icc (-ε) ε ∧
      ∀ f ∈ S, ∀ x : G, inverseCoefficient e L f x =
        (∫ s, a s * inverseCoefficient e M f (h.expG (s • X) * x)) +
          ∫ s, b s * inverseCoefficient e L f (h.expG (s • X) * x) := by
  let q (s : ℝ) := e.symm (h.expG (s • (-X)))
  have hq0 : q 0 = 1 := by simp [q, h.expG_zero]
  have hqa (s t : ℝ) : q (s + t) = q s * q t := by simp only [q, h.expG_add_smul, map_mul]
  obtain ⟨V, L₁, a, b, ha, hb, has, hbs, hEq⟩ :=
    exists_directional_factorization S hshift L.domain L.weight q hq0 hqa hsmooth hε hbound
  have hs : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  refine ⟨⟨V, L₁⟩, a, b, ha, hb, has.trans hs, hbs.trans hs, fun f hf x => ?_⟩
  let u := shift ((e.symm x)⁻¹) f
  have he (s : ℝ) : shift (q s) u = shift ((e.symm (h.expG (s • X) * x))⁻¹) f := by
    dsimp only [u, q]
    rw [shift_shift, map_mul, mul_inv_rev, smul_neg, h.expG_neg, map_inv]
  simpa only [he, inverseCoefficient, coefficient, u] using hEq u (hshift _ f hf)

omit [FiniteDimensional ℝ A] in
private theorem exists_finite_inverseCoefficient (S : Submodule ℂ C(H, ℂ))
    (hshift : ∀ a f, f ∈ S → shift a f ∈ S) {ε : ℝ} (hε : 0 < ε)
    (hsmooth : ∀ (B : Compacts H) (X : 𝔤), ∀ f ∈ S, ContDiff ℝ ∞
      (fun s : ℝ => restrict B (shift (e.symm (h.expG (s • (-X)))) f)))
    (hbound : ∀ (B : Compacts H) (X : 𝔤),
      LineDerivativeBounds S B (fun s : ℝ => e.symm (h.expG (s • (-X)))) ε) :
    ∀ {d : ℕ} (X : Fin d → 𝔤) (L : LocalFunctional H),
      ∃ (m : ℕ) (M : Fin m → LocalFunctional H) (K : Fin m → (Fin d → ℝ) → ℂ),
        (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ closedBall 0 ε) ∧
        ∀ f ∈ S, ∀ x : G, inverseCoefficient e L f x =
          ∑ i, ∫ t, K i t * inverseCoefficient e (M i) f (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X L
    refine ⟨1, fun _ => L, fun _ _ => 1, fun _ => ⟨contDiff_const, ?_⟩, ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]
      exact mem_closedBall_self hε.le
    · intro f _ x
      simp only [Fin.sum_univ_one, h.revProdExp_zero, one_mul, integral_const]
      have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      rw [hv, one_smul]
  | succ d ih =>
    intro X L
    obtain ⟨M, a, b, ha, hb, has, hbs, hLine⟩ := inverseCoefficient_factor_direction h e S hshift
      L (X 0) hε (hsmooth L.domain (X 0)) (hbound L.domain (X 0))
    obtain ⟨m₁, M₁, K₁, hK₁, h₁⟩ := ih (Fin.tail X) M
    obtain ⟨m₂, M₂, K₂, hK₂, h₂⟩ := ih (Fin.tail X) L
    refine ⟨m₁ + m₂, Fin.append M₁ M₂,
      Fin.append (fun i t => a (t 0) * K₁ i (Fin.tail t)) (fun i t => b (t 0) * K₂ i (Fin.tail t)),
      ?_, fun f hf x => ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using And.intro (contDiff_cons_kernel ha (hK₁ i).1)
          (tsupport_cons_kernel hε.le has (hK₁ i).2)
      · simpa only [Fin.append_right] using And.intro (contDiff_cons_kernel hb (hK₂ i).1)
          (tsupport_cons_kernel hε.le hbs (hK₂ i).2)
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hLine f hf x]
      have hc (D : LocalFunctional H) : Continuous (inverseCoefficient e D f) :=
        (continuous_coefficient D f).comp e.symm.continuous.inv
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le ha.continuous has (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => hc (M₁ i)) (h₁ f hf) x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hb.continuous hbs (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => hc (M₂ i)) (h₂ f hf) x).symm

end Product

section Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E H] [LieGroup 𝓘(ℝ, E) ∞ H]
  [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (measure : Measure H) [measure.IsHaarMeasure] [measure.IsMulRightInvariant]

local notation "I" => 𝓘(ℝ, E)

omit [T2Space H] [LocallyCompactSpace H] in
/-- A smooth compact average of translates of a compact functional is represented by a smooth
compact kernel, by exchanging the bounded functional with the two Bochner integrals. -/
private theorem exists_kernel_of_compact_average (L : LocalFunctional H) (κ : H → ℂ)
    (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ) :
    ∃ a : H → ℂ, ContMDiff I 𝓘(ℝ, ℂ) ∞ a ∧ HasCompactSupport a ∧
      ∀ f : C(H, ℂ), (∫ x, κ x * coefficient L f x ∂measure) = ∫ x, a x * f x ∂measure := by
  let B := L.domain
  let j : C(B, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let k (x : H) : C(B, ℂ) := ⟨fun y => κ (x * (j y)⁻¹),
    hκ.continuous.comp (continuous_const.mul j.continuous.inv)⟩
  have hκ' : ContMDiff (𝓘(ℝ, E).prod I) 𝓘(ℝ, ℂ) ∞ (fun p : H × H => κ (p.1 * p.2⁻¹)) :=
    hκ.comp (contMDiff_fst.mul contMDiff_snd.inv)
  have hk : ContMDiff I 𝓘(ℝ, C(B, ℂ)) ∞ k :=
    contMDiff_compactFamily_of_joint j hκ' (fun _ _ => rfl)
  have hkc : HasCompactSupport k := by
    apply HasCompactSupport.intro (hκc.isCompact.mul B.isCompact)
    intro x hx
    ext y
    change κ (x * (j y)⁻¹) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨_, h, j y, y.property, inv_mul_cancel_right _ _⟩
  refine ⟨fun x => L.weight (k x), (L.weight.restrictScalars ℝ).contDiff.contMDiff.comp hk,
    HasCompactSupport.comp_left (g := L.weight) hkc (map_zero _), fun f => ?_⟩
  let F (x : H) := κ x • restrict B (shift x f)
  let P (x : H) := f x • k x
  have hF : Continuous F := hκ.continuous.smul (by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_fst.mul (j.continuous.comp continuous_snd)))
  have hiF : Integrable F measure := hF.integrable_of_hasCompactSupport hκc.smul_right
  have hiP : Integrable P measure :=
    (f.continuous.smul hk.continuous).integrable_of_hasCompactSupport hkc.smul_left
  have heq : (∫ x, F x ∂measure) = ∫ x, P x ∂measure := by
    ext y
    let ev := ContinuousMap.evalCLM ℂ y (M := ℂ)
    change ev (∫ x, F x ∂measure) = ev (∫ x, P x ∂measure)
    rw [← ev.integral_comp_comm hiF, ← ev.integral_comp_comm hiP]
    change (∫ x, κ x * f (x * j y) ∂measure) = ∫ x, f x * κ (x * (j y)⁻¹) ∂measure
    rw [← integral_mul_right_eq_self (μ := measure) (fun x => f x * κ (x * (j y)⁻¹)) (j y)]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [mul_inv_cancel_right, mul_comm]
  calc
    _ = L.weight (∫ x, F x ∂measure) := by
      rw [← L.weight.integral_comp_comm hiF]
      simp only [F, map_smul, smul_eq_mul, coefficient, B]
    _ = L.weight (∫ x, P x ∂measure) := congrArg L.weight heq
    _ = _ := by
      rw [← L.weight.integral_comp_comm hiP]
      simp only [P, map_smul, smul_eq_mul, mul_comm (f _)]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {ρ : H →* Aˣ}

omit [T2Space H] [LocallyCompactSpace H] in
/-- A common compact bound for all orders in each smooth one-parameter subgroup gives a
smooth compactly supported reproducer for a left-translation invariant space of functions. -/
theorem exists_smoothCompact_reproducer (hρ : IsClosedLinearRealization I ρ) (S : Submodule ℂ C(H, ℂ))
    (hs : ∀ f ∈ S, ContMDiff I 𝓘(ℝ, ℂ) ∞ f)
    (hshift : ∀ a f, f ∈ S → shift a f ∈ S)
    (hbound : ∀ (B : Compacts H) (q : ℝ → H), ContMDiff 𝓘(ℝ) I ∞ q → q 0 = 1 →
      (∀ s t, q (s + t) = q s * q t) → ∀ ε > 0, LineDerivativeBounds S B q ε) :
    ∃ κ : H → ℂ, ContMDiff I 𝓘(ℝ, ℂ) ∞ κ ∧ HasCompactSupport κ ∧
      ∀ f ∈ S, f 1 = ∫ x, κ x * f x ∂measure := by
  classical
  let h := hρ.isExpLieAlgebra
  let e := hρ.rangeEquiv
  let 𝔤 := lieSubmodule ρ.range hρ.isClosed_range
  let := h.chartedSpace
  obtain ⟨he, he'⟩ := hρ.contMDiff_rangeRestrict_and_symm
  let : MeasurableSpace ρ.range := borel _
  let : BorelSpace ρ.range := ⟨rfl⟩
  let ν := measure.map e
  let : ν.IsHaarMeasure := e.isHaarMeasure_map measure
  let basis := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp ν basis
  let B₀ : Compacts H := ⟨{1}, isCompact_singleton⟩
  let L : LocalFunctional H := ⟨B₀, ContinuousMap.evalCLM ℂ ⟨1, mem_singleton _⟩⟩
  have cq (X : 𝔤) : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => e.symm (h.expG (s • (-X)))) := by
    apply he'.comp
    exact h.contMDiff_expG_comp (contDiff_id.smul contDiff_const)
  obtain ⟨m, M, K, hK, hExp⟩ := exists_finite_inverseCoefficient h e S hshift hε
    (fun _ X f hf => contMDiff_restrict_mul (cq X) (hs f hf))
    (fun B X => hbound B _ (cq X) (by simp [h.expG_zero])
      (fun s t => by simp only [h.expG_add_smul, map_mul]) ε hε) (⇑basis) L
  have hK' (i : Fin m) : ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ closedBall 0 ε := by
    refine ⟨(hK i).1.comp contDiff_neg, fun t ht => ?_⟩
    have ht' : -t ∈ tsupport (K i) := tsupport_comp_subset_preimage (K i)
      (f := fun t => -t) continuous_neg ht
    simpa only [mem_closedBall_zero_iff, norm_neg] using (hK i).2 ht'
  choose b hbs hbc _ hb using fun i => hdens ε le_rfl (fun t => K i (-t)) (hK' i).1 (hK' i).2
  let k (i : Fin m) := b i ∘ e
  have hks (i : Fin m) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (k i) := (hbs i).comp he
  have hkc (i : Fin m) : HasCompactSupport (k i) := (hbc i).comp_homeomorph e.toHomeomorph
  choose κ hκs hκc hκ using fun i => exists_kernel_of_compact_average measure (M i) (k i) (hks i) (hkc i)
  refine ⟨fun x => ∑ i, κ i x, ContMDiff.sum fun i _ => hκs i, ?_, fun f hf => ?_⟩
  · rw [show (fun x => ∑ i, κ i x) = ∑ i, κ i from by funext x; rw [Finset.sum_apply]]
    exact HasCompactSupport.finset_sum (fun i _ => hκc i)
  have hEval : inverseCoefficient e L f 1 = f 1 := by simp [inverseCoefficient, coefficient, L]
  have hBase := hExp f hf 1
  rw [hEval] at hBase
  rw [hBase]
  simp only [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (f := fun i x => κ i x * f x) (fun i _ =>
    ((hκs i).continuous.mul f.continuous).integrable_of_hasCompactSupport (hκc i).mul_right)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hκ i f]
  simp only [mul_one]
  let φ : ρ.range → ℂ := coefficient (M i) f ∘ e.symm
  have hφ : Continuous φ := (continuous_coefficient (M i) f).comp e.symm.continuous
  have heq : (∫ x, k i x * coefficient (M i) f x ∂measure) = ∫ x, b i x * φ x ∂ν := by
    change _ = ∫ x, b i x * φ x ∂(measure.map e.toHomeomorph.toMeasurableEquiv)
    rw [integral_map_equiv]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    change b i (e x) * coefficient (M i) f x = b i (e x) * coefficient (M i) f (e.symm (e x))
    rw [e.symm_apply_apply]
  rw [heq, hb i φ hφ]
  have ht (t : Fin (Module.finrank ℝ 𝔤) → ℝ) :
      K i (-t) * φ (h.prodExp (⇑basis) t) =
        (fun s => K i s * inverseCoefficient e (M i) f (h.revProdExp (⇑basis) s)) (-t) := by
    have hh := h.revProdExp_inv (⇑basis) (-t)
    rw [neg_neg] at hh
    simp only [inverseCoefficient, φ, Function.comp_apply, ← hh, map_inv]
  refine (integral_neg_eq_self
    (fun s => K i s * inverseCoefficient e (M i) f (h.revProdExp (⇑basis) s)) volume).symm.trans ?_
  exact integral_congr_ae (Eventually.of_forall fun t => (ht t).symm)

end Smoothing

end Langlands.Analysis.CompactFunctional
