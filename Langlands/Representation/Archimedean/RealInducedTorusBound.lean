import Langlands.Representation.Archimedean.RealInducedTorusReduction

/-!
# The torus-pairing bound

Let `p_1, …, p_r` be pairwise disjoint blocks of `GL_N(ℝ)` and let `T` be the torus of block
rotations. For smooth `u, h` with `IsExpEquivariant α_u u`, `IsExpEquivariant α_h h`, `u` right
`O(N)`-finite and `h` in the class of the multi-block bound, and for smooth right
`O(N)`-invariant `E_u, E_h` with real exponents `σ_u, σ_h` (tied at the blocks for `E_h`), there is
`C` with

`|∫_T u(τ y_1) h(τ y_2) dτ| ≤ C |∫_T E_u(τ y_1) E_h(τ y_2) dτ|` for all `y_1, y_2`

(`norm_coeffs_le_mul_norm_coeffs`, statement `RealInducedTorusBoundStatement`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealInducedTorusBound

open RealBlockRotation RealBlockFourierFinite RealInducedBlockSlice RealInducedBlockBound
  RealInducedBlockInvariance RealInducedTorusCore RealInducedTorusReduction RealBlockJacquet

variable {N : ℕ}

/-! ## Equivariance of translates and products -/

theorem isExpEquivariant_mul_right {α : Fin N → ℂ} {φ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : RealBlockDerivative.IsExpEquivariant α φ) (g : Langlands.GeneralLinear N ℝ) :
    RealBlockDerivative.IsExpEquivariant α fun x => φ (x * g) := by
  intro x n g'
  simp only
  rw [mul_assoc _ g' g]
  exact hφ x n (g' * g)

theorem isExpEquivariant_mul {α β : Fin N → ℂ} {φ ψ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : RealBlockDerivative.IsExpEquivariant α φ)
    (hψ : RealBlockDerivative.IsExpEquivariant β ψ) :
    RealBlockDerivative.IsExpEquivariant (α + β) fun x => φ x * ψ x := by
  intro x n g
  simp only
  rw [hφ x n g, hψ x n g]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.exp_add]
  ring

/-! ## Slots read off from a matrix -/

theorem mem_readSlots_zeroModes {S : List (Slot N)} {C : Matrix (Fin N) (Fin N) ℝ} {t : Slot N}
    (ht : t ∈ readSlots C (zeroModes S)) : ∃ s ∈ S, t = readSlot C (setMode s 0) := by
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht'
  exact ⟨s, hs, rfl⟩

theorem setMode_mem_zeroModes {S : List (Slot N)} {s : Slot N} (hs : s ∈ S) :
    setMode s 0 ∈ zeroModes S :=
  List.mem_map_of_mem hs

theorem coeffs_readSlots_zeroModes (S : List (Slot N)) (C : Matrix (Fin N) (Fin N) ℝ)
    (F : Langlands.GeneralLinear N ℝ → ℂ) :
    coeffs (zeroModes (readSlots C (zeroModes S))) F = coeffs (zeroModes S) F :=
  coeffs_congr_map _ _ (by simp [zeroModes, readSlots, readSlot, setMode, Function.comp_def]) F

theorem length_readSlots_zeroModes (S : List (Slot N)) (C : Matrix (Fin N) (Fin N) ℝ) :
    (readSlots C (zeroModes S)).length = S.length := by
  simp [readSlots, zeroModes]

theorem inClass_readSlots_zeroModes {S : List (Slot N)} {D : ℕ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : InClass S D F) (C : Matrix (Fin N) (Fin N) ℝ) :
    InClass (readSlots C (zeroModes S)) D F := by
  refine ⟨hF.1, hF.2.1, fun t ht => ?_⟩
  obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
  exact hF.2.2 s hs

theorem hasDegree_readSlots_zeroModes {S : List (Slot N)} {D : ℕ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : HasDegree S D F) (C : Matrix (Fin N) (Fin N) ℝ) :
    HasDegree (readSlots C (zeroModes S)) D F := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
  exact hF s hs

/-! ## Norms of the scalar factors -/

/-- `|χ_α(c)| = χ_σ(c)` for adapted `c` if `Re α_i = σ_i` away from the blocks. -/
theorem norm_chi_eq {L : List (Slot N)} {c : Langlands.GeneralLinear N ℝ} (hc : IsAdapted L c)
    {α : Fin N → ℂ} {σ : Fin N → ℝ}
    (h : ∀ i, (∀ s ∈ L, i ≠ ia s.hp ∧ i ≠ ib s.hp) → (α i).re = σ i) :
    ‖chi α c‖ = ‖chi (fun i => (σ i : ℂ)) c‖ := by
  rw [norm_chi, norm_chi]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re]
  by_cases hi : ∀ s ∈ L, i ≠ ia s.hp ∧ i ≠ ib s.hp
  · rw [h i hi]
  · push Not at hi
    obtain ⟨s, hs, hs'⟩ := hi
    have e : (c : Matrix (Fin N) (Fin N) ℝ) i i = 1 := by
      by_cases e : i = ia s.hp
      · rw [e]
        exact (hc.2.2 s hs).1
      · rw [hs' e]
        exact (hc.2.2 s hs).2.1
    rw [e, Real.log_one, mul_zero, mul_zero]

/-- `|detFactor α L| = detFactor σ L` if `Re α = σ` at the first indices of the blocks. -/
theorem norm_detFactor_eq {α : Fin N → ℂ} {σ : Fin N → ℝ} :
    ∀ (L : List (Slot N)), (∀ s ∈ L, (α (ia s.hp)).re = σ (ia s.hp)) →
      ‖detFactor α L‖ = ‖detFactor (fun i => (σ i : ℂ)) L‖
  | [], _ => by simp [detFactor]
  | s :: L, h => by
    have ih := norm_detFactor_eq L fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hs := h s List.mem_cons_self
    simp only [detFactor, List.map_cons, List.prod_cons, norm_mul] at ih ⊢
    rw [ih, Complex.norm_exp, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, hs]

theorem expBound_cons (s : Slot N) (L : List (Slot N)) :
    expBound (s :: L) =
      Real.exp ((s.α.re - s.M / 2) * (s.x + s.y)) / ‖waveU s.x s.y s.w‖ * expBound L := by
  simp [expBound]

theorem expBound_nonneg : ∀ L : List (Slot N), 0 ≤ expBound L
  | [] => by simp [expBound]
  | s :: L => by
    rw [expBound_cons]
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (norm_nonneg _)) (expBound_nonneg L)

/-- The lower bound `π^r · expBound ≤ |∏_s e^{σ_s (x_s + y_s)} I(x_s, y_s, w_s)|` for
`σ_s = Re α_s − M_s/2`. -/
theorem pi_pow_mul_expBound_le (σ : Slot N → ℝ) :
    ∀ L : List (Slot N), (∀ s ∈ L, σ s = s.α.re - (s.M : ℝ) / 2) →
      Real.pi ^ L.length * expBound L ≤
        ‖(L.map fun s => Complex.exp ((σ s : ℂ) * ((s.x : ℂ) + s.y)) *
          (invIntegral s.x s.y s.w : ℂ)).prod‖
  | [], _ => by simp [expBound]
  | s :: L, h => by
    have ih := pi_pow_mul_expBound_le σ L fun t ht => h t (List.mem_cons_of_mem _ ht)
    have h1 : ‖Complex.exp ((σ s : ℂ) * ((s.x : ℂ) + s.y))‖ = Real.exp (σ s * (s.x + s.y)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have h2 : ‖(invIntegral s.x s.y s.w : ℂ)‖ = invIntegral s.x s.y s.w := by
      rw [Complex.norm_real, Real.norm_of_nonneg (invIntegral_pos _ _ _).le]
    have h3 := pi_div_le_invIntegral s.x s.y s.w
    rw [List.map_cons, List.prod_cons, norm_mul, norm_mul, h1, h2, h s List.mem_cons_self,
      expBound_cons, List.length_cons, pow_succ]
    have hE := Real.exp_pos ((s.α.re - (s.M : ℝ) / 2) * (s.x + s.y))
    calc Real.pi ^ L.length * Real.pi *
          (Real.exp ((s.α.re - (s.M : ℝ) / 2) * (s.x + s.y)) / ‖waveU s.x s.y s.w‖ *
            expBound L)
        = (Real.exp ((s.α.re - (s.M : ℝ) / 2) * (s.x + s.y)) *
            (Real.pi / ‖waveU s.x s.y s.w‖)) * (Real.pi ^ L.length * expBound L) := by ring
      _ ≤ (Real.exp ((s.α.re - (s.M : ℝ) / 2) * (s.x + s.y)) * invIntegral s.x s.y s.w) *
            ‖(L.map fun s => Complex.exp ((σ s : ℂ) * ((s.x : ℂ) + s.y)) *
              (invIntegral s.x s.y s.w : ℂ)).prod‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3 hE.le) ih
            (mul_nonneg (pow_nonneg Real.pi_pos.le _) (expBound_nonneg L))
            (mul_nonneg hE.le (invIntegral_pos _ _ _).le)

/-! ## The reduction of a torus pairing -/

/-- **Reduction of a torus pairing.** Let `y_1 = c_1 · (Y_1 · k_1)` and
`Y_1⁻¹ y_2 = c_3 · (Y_3 · k_3)` with `c_1, c_3` adapted and `Y_i = point (readSlots C_i Z)`.
For smooth `φ, ψ` with `IsExpEquivariant a φ`, `IsExpEquivariant b ψ` and
`(a + b)_p − (a + b)_{p+1} = 2` at the blocks,
`∫_T φ(τ y_1) ψ(τ y_2) = χ_a(c_1) · detFactor (a + b) · χ_b(c_3) · ∫_T φ(τ k_1) ψ(τ Y_3 k_3)`. -/
theorem coeffs_reduce {S : List (Slot N)} (hpw : S.Pairwise Slot.Disjoint)
    {φ ψ : Langlands.GeneralLinear N ℝ → ℂ} {a b : Fin N → ℂ}
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) (ha : RealBlockDerivative.IsExpEquivariant a φ)
    (hψ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ ψ) (hb : RealBlockDerivative.IsExpEquivariant b ψ)
    (h2 : ∀ s ∈ S, a (ia s.hp) + b (ia s.hp) - (a (ib s.hp) + b (ib s.hp)) = 2)
    {C1 C3 : Matrix (Fin N) (Fin N) ℝ} {c1 c3 k1 k3 y2 : Langlands.GeneralLinear N ℝ}
    (hc1 : IsAdapted (zeroModes S) c1) (hc3 : IsAdapted (zeroModes S) c3)
    (hy3 : (point (readSlots C1 (zeroModes S)))⁻¹ * y2 =
      c3 * (point (readSlots C3 (zeroModes S)) * k3)) :
    coeffs (zeroModes S)
        (fun x => φ (x * (c1 * (point (readSlots C1 (zeroModes S)) * k1))) * ψ (x * y2)) 1 =
      chi a c1 * detFactor (a + b) (readSlots C1 (zeroModes S)) * chi b c3 *
        coeffs (zeroModes S)
          (fun x => φ (x * k1) * ψ (x * (point (readSlots C3 (zeroModes S)) * k3))) 1 := by
  set Z := zeroModes S with hZ
  have hpwZ : Z.Pairwise Slot.Disjoint := pairwise_zeroModes hpw
  set Z1 := readSlots C1 Z with hZ1
  set Y1 := point Z1 with hY1
  rw [coeffs_mul_adapted hpwZ ha hc1 (Y1 * k1) (fun x => ψ (x * y2))]
  set G : Langlands.GeneralLinear N ℝ → ℂ := fun x => φ (x * k1) * ψ (x * (Y1⁻¹ * y2)) with hG
  have e1 : (fun x => φ (x * (Y1 * k1)) * ψ (x * y2)) = fun x => G (x * Y1) := by
    funext x
    show _ = φ (x * Y1 * k1) * ψ (x * Y1 * (Y1⁻¹ * y2))
    rw [mul_assoc x Y1 k1, mul_assoc x Y1, mul_inv_cancel_left]
  have hGs : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ G :=
    RealPrincipalSeriesDuality.contMDiff_mul_fun (hφ.comp contMDiff_mul_right)
      (hψ.comp contMDiff_mul_right)
  have hGα : RealBlockDerivative.IsExpEquivariant (a + b) G :=
    isExpEquivariant_mul (isExpEquivariant_mul_right ha k1) (isExpEquivariant_mul_right hb _)
  have hpw1 : Z1.Pairwise Slot.Disjoint := pairwise_readSlots C1 hpwZ
  have hj1 : ∀ s ∈ Z1, s.j = 0 := by
    intro t ht
    obtain ⟨s, _, rfl⟩ := mem_readSlots_zeroModes ht
    rfl
  have hδ1 : ∀ s ∈ Z1, (a + b) (ia s.hp) - (a + b) (ib s.hp) = 2 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
    simpa only [Pi.add_apply] using h2 s hs
  have hpm := coeffs_point_mul hGs hGα Z1 hpw1 hj1 hδ1 1
  rw [mul_one, coeffs_readSlots] at hpm
  rw [e1, ← coeffs_mul_right G Y1 Z 1, one_mul, hpm]
  have e2 : G = fun x => φ (x * k1) * ψ (x * (c3 * (point (readSlots C3 Z) * k3))) := by
    rw [hG, hy3]
  rw [e2, coeffs_mul_adapted' hpwZ hb hc3 (point (readSlots C3 Z) * k3) (fun x => φ (x * k1))]
  ring

/-! ## The torus-pairing bound -/

/-- **Torus-pairing bound.** -/
theorem norm_coeffs_le_mul_norm_coeffs (D : ℕ) {S : List (Slot N)}
    (hpw : S.Pairwise Slot.Disjoint) {αu αh : Fin N → ℂ} {σu σh : Fin N → ℝ}
    {u h Eu Eh : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ u)
    (huα : RealBlockDerivative.IsExpEquivariant αu u) (huK : IsKFin u) (hdeg : HasDegree S D u)
    (hh : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ h)
    (hhα : RealBlockDerivative.IsExpEquivariant αh h) (hcl : InClass S D h)
    (hEu : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ Eu)
    (hEuσ : RealBlockDerivative.IsExpEquivariant (fun i => (σu i : ℂ)) Eu)
    (hEuK : ∀ g, ∀ k ∈ unitaryCompact ℝ N, Eu (g * k) = Eu g) (hEu1 : Eu 1 = 1)
    (hEh : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ Eh)
    (hEhσ : RealBlockDerivative.IsExpEquivariant (fun i => (σh i : ℂ)) Eh)
    (hEhK : ∀ g, ∀ k ∈ unitaryCompact ℝ N, Eh (g * k) = Eh g) (hEh1 : Eh 1 = 1)
    (hα2 : ∀ s ∈ S, αu (ia s.hp) + αh (ia s.hp) - (αu (ib s.hp) + αh (ib s.hp)) = 2)
    (hσ2 : ∀ s ∈ S, σu (ia s.hp) + σh (ia s.hp) - (σu (ib s.hp) + σh (ib s.hp)) = 2)
    (hre : ∀ s ∈ S, (αu (ia s.hp) + αh (ia s.hp)).re = σu (ia s.hp) + σh (ia s.hp))
    (hσh1 : ∀ s ∈ S, σh (ib s.hp) = σh (ia s.hp) - 1)
    (hσhα : ∀ s ∈ S, σh (ia s.hp) = s.α.re - (s.M : ℝ) / 2)
    (hoff : ∀ i, (∀ s ∈ S, i ≠ ia s.hp ∧ i ≠ ib s.hp) → (αu i).re = σu i ∧ (αh i).re = σh i) :
    ∃ C : ℝ, ∀ y1 y2 : Langlands.GeneralLinear N ℝ,
      ‖coeffs (zeroModes S) (fun x => u (x * y1) * h (x * y2)) 1‖ ≤
        C * ‖coeffs (zeroModes S) (fun x => Eu (x * y1) * Eh (x * y2)) 1‖ := by
  set Z := zeroModes S with hZ
  have hpwZ : Z.Pairwise Slot.Disjoint := pairwise_zeroModes hpw
  have hKc : IsCompact (unitaryCompact ℝ N : Set (Langlands.GeneralLinear N ℝ)) := by
    have := RealPrincipalSeriesDuality.compactSpace_unitaryCompact N
    exact isCompact_iff_compactSpace.mpr this
  obtain ⟨A, hA⟩ := hKc.exists_bound_of_continuousOn hu.continuous.continuousOn
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcl.1.continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 (one_mem _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (one_mem _))
  set K0 := coreConst S.length D * A * B with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg (mul_nonneg (coreConst_nonneg _ _) hA0) hB0
  have hπ : 0 < Real.pi ^ S.length := pow_pos Real.pi_pos _
  refine ⟨K0 / Real.pi ^ S.length, fun y1 y2 => ?_⟩
  obtain ⟨C1, c1, k1, hk1, hc1, rfl⟩ := exists_decomp hpwZ y1
  obtain ⟨C3, c3, k3, hk3, hc3, hy3⟩ := exists_decomp hpwZ ((point (readSlots C1 Z))⁻¹ * y2)
  set Z1 := readSlots C1 Z with hZ1
  set Z3 := readSlots C3 Z with hZ3
  -- the reductions
  rw [coeffs_reduce hpw hu huα hh hhα hα2 hc1 hc3 hy3,
    coeffs_reduce hpw hEu hEuσ hEh hEhσ (fun s hs => by
      have := congrArg (fun r : ℝ => (r : ℂ)) (hσ2 s hs)
      push_cast at this
      exact this) hc1 hc3 hy3]
  simp only [norm_mul]
  -- the scalar factors agree in norm
  have hoffZ : ∀ i, (∀ s ∈ Z, i ≠ ia s.hp ∧ i ≠ ib s.hp) →
      (αu i).re = σu i ∧ (αh i).re = σh i := fun i hi =>
    hoff i fun s hs => hi (setMode s 0) (setMode_mem_zeroModes hs)
  have n1 : ‖chi αu c1‖ = ‖chi (fun i => (σu i : ℂ)) c1‖ :=
    norm_chi_eq hc1 fun i hi => (hoffZ i hi).1
  have n3 : ‖chi αh c3‖ = ‖chi (fun i => (σh i : ℂ)) c3‖ :=
    norm_chi_eq hc3 fun i hi => (hoffZ i hi).2
  have n2 : ‖detFactor (αu + αh) Z1‖ =
      ‖detFactor ((fun i => (σu i : ℂ)) + fun i => (σh i : ℂ)) Z1‖ := by
    have := norm_detFactor_eq (α := αu + αh) (σ := σu + σh) Z1 (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
      simpa only [Pi.add_apply] using hre s hs)
    rw [this]
    congr 2
    funext i
    simp
  rw [n1, n2, n3]
  set X := ‖chi (fun i => (σu i : ℂ)) c1‖ *
    ‖detFactor ((fun i => (σu i : ℂ)) + fun i => (σh i : ℂ)) Z1‖ *
      ‖chi (fun i => (σh i : ℂ)) c3‖ with hX
  have hX0 : 0 ≤ X := by positivity
  -- the core bound
  have hcore : ‖coeffs Z (fun x => u (x * k1) * h (x * (point Z3 * k3))) 1‖ ≤
      K0 * expBound Z3 := by
    have := norm_coeffs_zeroModes_le D (slots := Z3) (pairwise_readSlots C3 hpwZ) hu.continuous
      huK (hasDegree_readSlots_zeroModes hdeg C3) hA (inClass_readSlots_zeroModes hcl C3) hB hk1
      hk3
    rwa [coeffs_readSlots_zeroModes, length_readSlots_zeroModes] at this
  -- the exact value of the comparison average
  have hEval : coeffs Z (fun x => Eu (x * k1) * Eh (x * (point Z3 * k3))) 1 =
      (Z3.map fun s => Complex.exp (((σh (ia s.hp) : ℝ) : ℂ) * ((s.x : ℂ) + s.y)) *
        (invIntegral s.x s.y s.w : ℂ)).prod := by
    have e1 : coeffs Z (fun x => Eu (x * k1) * Eh (x * (point Z3 * k3))) 1 =
        coeffs Z (fun x => Eh (x * point Z3)) 1 := by
      refine coeffs_congr_torus Z 1 fun x hx => ?_
      have hxK : x * 1 ∈ unitaryCompact ℝ N := by
        rw [mul_one]
        exact torus_le_unitaryCompact Z hx
      have hu1 : Eu (x * 1 * k1) = 1 := by
        have := hEuK 1 (x * 1 * k1) (mul_mem hxK hk1)
        rw [one_mul] at this
        rw [this, hEu1]
      show Eu (x * 1 * k1) * Eh (x * 1 * (point Z3 * k3)) = Eh (x * 1 * point Z3)
      rw [hu1, one_mul, ← mul_assoc, hEhK _ k3 hk3]
    have hcov : ∀ s ∈ Z3, IsBlockCovariant s.hp ((σh (ia s.hp) : ℝ) : ℂ)
        (((σh (ia s.hp) : ℝ) : ℂ) - 1) Eh := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
      have hc := isBlockCovariant_of_isExpEquivariant s.hp hEhσ
      have e : ((σh (ib s.hp) : ℝ) : ℂ) = ((σh (ia s.hp) : ℝ) : ℂ) - 1 := by
        rw [hσh1 s hs]
        push_cast
        ring
      rw [e] at hc
      exact hc
    have hpt := coeffs_zeroModes_point (fun s => ((σh (ia s.hp) : ℝ) : ℂ)) hEh.continuous hEhK
      Z3 (pairwise_readSlots C3 hpwZ) hcov
    rw [coeffs_readSlots_zeroModes, hEh1, mul_one] at hpt
    rw [e1, show coeffs Z (fun x => Eh (x * point Z3)) 1 = coeffs Z Eh (1 * point Z3) from
      (coeffs_mul_right Eh (point Z3) Z 1).symm, one_mul, hpt]
  have hlow : Real.pi ^ S.length * expBound Z3 ≤
      ‖coeffs Z (fun x => Eu (x * k1) * Eh (x * (point Z3 * k3))) 1‖ := by
    rw [hEval, ← length_readSlots_zeroModes S C3]
    refine pi_pow_mul_expBound_le (fun s => σh (ia s.hp)) Z3 fun t ht => ?_
    obtain ⟨s, hs, rfl⟩ := mem_readSlots_zeroModes ht
    exact hσhα s hs
  calc X * ‖coeffs Z (fun x => u (x * k1) * h (x * (point Z3 * k3))) 1‖
      ≤ X * (K0 * expBound Z3) := mul_le_mul_of_nonneg_left hcore hX0
    _ = K0 / Real.pi ^ S.length * (X * (Real.pi ^ S.length * expBound Z3)) := by
        field_simp
    _ ≤ K0 / Real.pi ^ S.length *
          (X * ‖coeffs Z (fun x => Eu (x * k1) * Eh (x * (point Z3 * k3))) 1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow hX0) (div_nonneg hK00 hπ.le)

end RealInducedTorusBound

open RealInducedBlockBound RealInducedTorusCore RealBlockRotation in
/-- **Torus-pairing bound.** Let `S` be pairwise disjoint slots and `T` the torus of their block
rotations. Let `u, h` be smooth with `IsExpEquivariant α_u u`, `IsExpEquivariant α_h h`, `u` right
`O(N)`-finite of degree `≤ D` along the blocks and `h ∈ InClass S D`. Let `E_u, E_h` be smooth,
right `O(N)`-invariant, `IsExpEquivariant` with real exponents `σ_u, σ_h`, and `E_u(1) = E_h(1) = 1`.
Assume at every block `p` of a slot `s`: `(α_u + α_h)_p − (α_u + α_h)_{p+1} = 2`,
`(σ_u + σ_h)_p − (σ_u + σ_h)_{p+1} = 2`, `Re (α_u + α_h)_p = (σ_u + σ_h)_p`,
`σ_{h,p+1} = σ_{h,p} − 1` and `σ_{h,p} = Re α_s − M_s/2`, and away from the blocks
`Re α_u = σ_u`, `Re α_h = σ_h`. Then there is `C` with
`|∫_T u(τ y_1) h(τ y_2) dτ| ≤ C |∫_T E_u(τ y_1) E_h(τ y_2) dτ|` for all `y_1, y_2`. -/
def RealInducedTorusBoundStatement : Prop :=
  ∀ (N D : ℕ) (S : List (Slot N)), S.Pairwise Slot.Disjoint →
    ∀ (αu αh : Fin N → ℂ) (σu σh : Fin N → ℝ) (u h Eu Eh : Langlands.GeneralLinear N ℝ → ℂ),
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ u → RealBlockDerivative.IsExpEquivariant αu u →
    IsKFin u → HasDegree S D u →
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ h → RealBlockDerivative.IsExpEquivariant αh h →
    InClass S D h →
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ Eu →
    RealBlockDerivative.IsExpEquivariant (fun i => (σu i : ℂ)) Eu →
    (∀ g, ∀ k ∈ unitaryCompact ℝ N, Eu (g * k) = Eu g) → Eu 1 = 1 →
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ Eh →
    RealBlockDerivative.IsExpEquivariant (fun i => (σh i : ℂ)) Eh →
    (∀ g, ∀ k ∈ unitaryCompact ℝ N, Eh (g * k) = Eh g) → Eh 1 = 1 →
    (∀ s ∈ S, αu (ia s.hp) + αh (ia s.hp) - (αu (ib s.hp) + αh (ib s.hp)) = 2) →
    (∀ s ∈ S, σu (ia s.hp) + σh (ia s.hp) - (σu (ib s.hp) + σh (ib s.hp)) = 2) →
    (∀ s ∈ S, (αu (ia s.hp) + αh (ia s.hp)).re = σu (ia s.hp) + σh (ia s.hp)) →
    (∀ s ∈ S, σh (ib s.hp) = σh (ia s.hp) - 1) →
    (∀ s ∈ S, σh (ia s.hp) = s.α.re - (s.M : ℝ) / 2) →
    (∀ i, (∀ s ∈ S, i ≠ ia s.hp ∧ i ≠ ib s.hp) → (αu i).re = σu i ∧ (αh i).re = σh i) →
    ∃ C : ℝ, ∀ y1 y2 : Langlands.GeneralLinear N ℝ,
      ‖coeffs (zeroModes S) (fun x => u (x * y1) * h (x * y2)) 1‖ ≤
        C * ‖coeffs (zeroModes S) (fun x => Eu (x * y1) * Eh (x * y2)) 1‖

theorem realInducedTorusBound : RealInducedTorusBoundStatement :=
  fun _ D _ hpw _ _ _ _ _ _ _ _ hu huα huK hdeg hh hhα hcl hEu hEuσ hEuK hEu1 hEh hEhσ hEhK hEh1
    hα2 hσ2 hre hσh1 hσhα hoff =>
  RealInducedTorusBound.norm_coeffs_le_mul_norm_coeffs D hpw hu huα huK hdeg hh hhα hcl hEu hEuσ
    hEuK hEu1 hEh hEhσ hEhK hEh1 hα2 hσ2 hre hσh1 hσhα hoff

end Langlands.Archimedean
