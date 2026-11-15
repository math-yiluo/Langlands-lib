import Langlands.Representation.Archimedean.RealJacquetRadialFiniteness
import Mathlib.Analysis.ODE.Gronwall

/-!
# Casselman's vanishing argument for an abstract family of matrix coefficients

Let `(π, V)` be a `𝔤𝔩_n(ℝ)`-module and let `ℓ s ψ v` be a family of bilinear forms, indexed by a
real parameter `s`, on a space `P` of "dual vectors" `ψ` and on `V`. Think of
`ℓ s ψ v = ∫_{O(n)} w(k a_s) ψ(k) dk` for `v` the image of `w` and `a_s = exp(s H)`,
`H = diag(h)` with `h` strictly increasing. Assume

* (adjoint) `ℓ s ψ (E_{ab} v) = -e^{s (h_a - h_b)} ℓ s (R_{ab} ψ) v`;
* (derivative) `d/ds ℓ s ψ v = ℓ s ψ (H v)`;
* (growth) `‖ℓ s ψ v‖ ≤ C e^{c s}` for `s ≥ 0`, with `c` independent of `ψ` and `v`.

If `𝔫V = V`, then the matrix coefficients decay faster than every exponential
(`decay`), and the radial finiteness of `RealJacquetRadialFiniteness` together with Gronwall's
inequality shows that `ℓ s₀ ψ v = 0` for every `s₀ > 0`, every `ψ` in a finite-dimensional space
stable under the `R_{ab} - R_{ba}` and every `v` in a finite-dimensional `𝔨`-stable space
(`eq_zero`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealJacquetGronwall

open RealJacquetFiniteGeneration

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {P : Type*} [AddCommGroup P] [Module ℂ P]
  {ℓ : ℝ → P →ₗ[ℂ] V →ₗ[ℂ] ℂ} {R : Fin n → Fin n → P →ₗ[ℂ] P} {h : Fin n → ℝ}

/-! ## Decay -/

section Decay

variable (ℓ) in
/-- The vectors whose matrix coefficients decay like `e^{(c - k) s}`. -/
def decaySpace (c : ℝ) (k : ℕ) : Submodule ℂ V where
  carrier := {v | ∀ ψ : P, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → ‖ℓ s ψ v‖ ≤ C * Real.exp ((c - k) * s)}
  zero_mem' ψ := ⟨0, fun s _ => by simp⟩
  add_mem' {v w} hv hw ψ := by
    obtain ⟨C₁, h₁⟩ := hv ψ
    obtain ⟨C₂, h₂⟩ := hw ψ
    refine ⟨C₁ + C₂, fun s hs => ?_⟩
    rw [map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ s hs) (h₂ s hs))
  smul_mem' a v hv ψ := by
    obtain ⟨C, hC⟩ := hv ψ
    refine ⟨‖a‖ * C, fun s hs => ?_⟩
    rw [map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs) (norm_nonneg _)

theorem exp_mul_sub_le {a b : Fin n} (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1) (hab : a < b)
    {s : ℝ} (hs : 0 ≤ s) : Real.exp (s * (h a - h b)) ≤ Real.exp (-s) := by
  apply Real.exp_le_exp.mpr
  nlinarith [hh a b hab]

/-- **Decay.** If `𝔫V = V`, every matrix coefficient decays like `e^{(c - k) s}` for every `k`. -/
theorem decay (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1)
    (hadj : ∀ (s : ℝ) (ψ : P) (v : V) (a b : Fin n),
      ℓ s ψ (op π (E a b) v) = -((Real.exp (s * (h a - h b)) : ℝ) : ℂ) * ℓ s (R a b ψ) v)
    {c : ℝ} (hgrowth : ∀ (ψ : P) (v : V), ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
      ‖ℓ s ψ v‖ ≤ C * Real.exp (c * s))
    (htop : realJacquetSubspace n π = ⊤) (k : ℕ) : decaySpace ℓ c k = ⊤ := by
  induction k with
  | zero =>
    rw [eq_top_iff]
    intro v _ ψ
    obtain ⟨C, hC⟩ := hgrowth ψ v
    exact ⟨C, fun s hs => by simpa using hC s hs⟩
  | succ k ih =>
    rw [eq_top_iff, ← htop, realJacquetSubspace, Submodule.span_le]
    rintro _ ⟨X, v, hX, rfl⟩
    change op π X v ∈ decaySpace ℓ c (k + 1)
    rw [op_eq_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [LinearMap.smul_apply]
    rcases lt_or_ge a b with hab | hba
    · refine Submodule.smul_mem _ _ ?_
      intro ψ
      obtain ⟨C, hC⟩ := (ih ▸ Submodule.mem_top : v ∈ decaySpace ℓ c k) (R a b ψ)
      refine ⟨C, fun s hs => ?_⟩
      rw [hadj, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have h1 := exp_mul_sub_le hh hab hs
      have h2 := hC s hs
      have hC0 : 0 ≤ C * Real.exp ((c - k) * s) := (norm_nonneg _).trans h2
      calc Real.exp (s * (h a - h b)) * ‖ℓ s (R a b ψ) v‖
          ≤ Real.exp (-s) * (C * Real.exp ((c - k) * s)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = C * Real.exp ((c - ((k + 1 : ℕ) : ℝ)) * s) := by
            rw [mul_left_comm, ← Real.exp_add]
            push_cast
            ring_nf
    · have hX0 : X a b = 0 := hX a b (by exact_mod_cast hba)
      rw [hX0, Complex.ofReal_zero, zero_smul]
      exact zero_mem _

end Decay

/-! ## Functions bounded by the box coefficients -/

section Bounded

variable (ℓ) {m p : ℕ} (bB : Fin m → V) (bΨ : Fin p → P) (s₀ : ℝ)

/-- `N(t) = ∑_{i,j} ‖ℓ t (bΨ j) (bB i)‖`. -/
def normSum (t : ℝ) : ℝ := ∑ i, ∑ j, ‖ℓ t (bΨ j) (bB i)‖

theorem normSum_nonneg (t : ℝ) : 0 ≤ normSum ℓ bB bΨ t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_le_normSum (t : ℝ) (i : Fin m) (j : Fin p) :
    ‖ℓ t (bΨ j) (bB i)‖ ≤ normSum ℓ bB bΨ t := by
  unfold normSum
  calc ‖ℓ t (bΨ j) (bB i)‖ ≤ ∑ j', ‖ℓ t (bΨ j') (bB i)‖ :=
        Finset.single_le_sum (f := fun j' => ‖ℓ t (bΨ j') (bB i)‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖ℓ t (bΨ j') (bB i')‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖ℓ t (bΨ j') (bB i')‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- Functions on `[s₀, ∞)` whose coefficients against `bΨ` are bounded by a multiple of `N`. -/
def boundedSpace : Submodule ℂ (Set.Ici s₀ → V) where
  carrier := {f | ∃ C : ℝ, ∀ (q : Set.Ici s₀) (j : Fin p),
    ‖ℓ q (bΨ j) (f q)‖ ≤ C * normSum ℓ bB bΨ q}
  zero_mem' := ⟨0, fun q j => by simp⟩
  add_mem' {f g} hf hg := by
    obtain ⟨C₁, h₁⟩ := hf
    obtain ⟨C₂, h₂⟩ := hg
    refine ⟨C₁ + C₂, fun q j => ?_⟩
    rw [Pi.add_apply, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ q j) (h₂ q j))
  smul_mem' a f hf := by
    obtain ⟨C, hC⟩ := hf
    refine ⟨‖a‖ * C, fun q j => ?_⟩
    rw [Pi.smul_apply, map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC q j) (norm_nonneg _)

variable {ℓ bB bΨ s₀}

theorem bound_of_mem_span {f : Set.Ici s₀ → V} (hf : f ∈ boundedSpace ℓ bB bΨ s₀) {ψ : P}
    (hψ : ψ ∈ Submodule.span ℂ (Set.range bΨ)) :
    ∃ C : ℝ, ∀ q : Set.Ici s₀, ‖ℓ q ψ (f q)‖ ≤ C * normSum ℓ bB bΨ q := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hψ
  obtain ⟨C, hC⟩ := hf
  refine ⟨(∑ j, ‖c j‖) * C, fun q => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC q j) (norm_nonneg _)

theorem bound_of_mem_span_family {f : Set.Ici s₀ → V} (hf : f ∈ boundedSpace ℓ bB bΨ s₀)
    {ι : Type*} [Fintype ι] {ψ : ι → P} (hψ : ∀ j, ψ j ∈ Submodule.span ℂ (Set.range bΨ)) :
    ∃ C : ℝ, ∀ (q : Set.Ici s₀) (j : ι), ‖ℓ q (ψ j) (f q)‖ ≤ C * normSum ℓ bB bΨ q := by
  choose C hC using fun j => bound_of_mem_span hf (hψ j)
  refine ⟨∑ j, |C j|, fun q j => (hC j q).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (normSum_nonneg ℓ bB bΨ q)
  exact Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem constMap_mem_boundedSpace {u : V} (hu : u ∈ Submodule.span ℂ (Set.range bB)) :
    RealJacquetRadial.constMap (Set.Ici s₀) V u ∈ boundedSpace ℓ bB bΨ s₀ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  refine ⟨∑ i, ‖c i‖, fun q j => ?_⟩
  rw [RealJacquetRadial.constMap_apply, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_le_normSum ℓ bB bΨ q i j) (norm_nonneg _)

end Bounded

/-! ## Radial stability -/

section Radial

variable {m p : ℕ} {bB : Fin m → V} {bΨ : Fin p → P} {s₀ : ℝ}

variable (h s₀) in
/-- The radial parameters `r_{ab}(q) = e^{q (h_a - h_b)}`. -/
def radialParam : Set.Ici s₀ → Fin n → Fin n → ℝ := fun q a b => Real.exp (q * (h a - h b))

theorem radialParam_le (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1) (hs₀ : 0 < s₀)
    (q : Set.Ici s₀) {a b : Fin n} (hab : a < b) : radialParam h s₀ q a b ≤ Real.exp (-s₀) := by
  apply Real.exp_le_exp.mpr
  have h1 := hh a b hab
  have hq : s₀ ≤ (q : ℝ) := q.2
  nlinarith

theorem radialParam_lt_one (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1) (hs₀ : 0 < s₀)
    (q : Set.Ici s₀) {a b : Fin n} (hab : a < b) : radialParam h s₀ q a b < 1 :=
  (radialParam_le hh hs₀ q hab).trans_lt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs₀))

theorem radialParam_sq_ne_one (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1) (hs₀ : 0 < s₀)
    (q : Set.Ici s₀) (a b : Fin n) (hab : a < b) : radialParam h s₀ q a b ^ 2 ≠ 1 := by
  have h1 := radialParam_lt_one hh hs₀ q hab
  have h0 : 0 < radialParam h s₀ q a b := Real.exp_pos _
  nlinarith

theorem isRadialStable_boundedSpace (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1) (hs₀ : 0 < s₀)
    (hadj : ∀ (s : ℝ) (ψ : P) (v : V) (a b : Fin n),
      ℓ s ψ (op π (E a b) v) = -((Real.exp (s * (h a - h b)) : ℝ) : ℂ) * ℓ s (R a b ψ) v)
    {Ψ : Submodule ℂ P} (hΨspan : Ψ ≤ Submodule.span ℂ (Set.range bΨ)) (hbΨ : ∀ j, bΨ j ∈ Ψ)
    (hΨ : ∀ a b : Fin n, ∀ ψ ∈ Ψ, R a b ψ - R b a ψ ∈ Ψ) :
    RealJacquetRadial.IsRadialStable π (radialParam h s₀) (boundedSpace ℓ bB bΨ s₀) where
  letter_mem a b hab f hf := by
    obtain ⟨C, hC⟩ := bound_of_mem_span_family hf
      (ψ := fun j => R a b (bΨ j) - R b a (bΨ j)) (fun j => hΨspan (hΨ a b _ (hbΨ j)))
    refine ⟨C, fun q j => ?_⟩
    set e₁ := Real.exp ((q : ℝ) * (h a - h b)) with he₁
    set e₂ := Real.exp ((q : ℝ) * (h b - h a)) with he₂
    have he : (e₁ : ℂ) * (e₂ : ℂ) = 1 := by
      have : e₁ * e₂ = 1 := by
        rw [he₁, he₂, ← Real.exp_add, show (q : ℝ) * (h a - h b) + q * (h b - h a) = 0 by ring,
          Real.exp_zero]
      exact_mod_cast this
    have key : ℓ q (bΨ j) (RealJacquetRadial.radLetter π (radialParam h s₀) a b f q) =
        -(e₁ : ℂ) * ℓ q (R a b (bΨ j) - R b a (bΨ j)) (f q) := by
      rw [RealJacquetRadial.radLetter_apply, op_sub, op_real_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, map_sub, map_smul, hadj, hadj, map_sub, LinearMap.sub_apply]
      simp only [radialParam, smul_eq_mul]
      rw [← he₁, ← he₂]
      push_cast
      linear_combination ((e₁ : ℂ) * ℓ q (R b a (bΨ j)) (f q)) * he
    rw [key, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : e₁ ≤ 1 := (radialParam_lt_one hh hs₀ q hab).le
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hC q j)
  sq_mem a b hab f hf := by
    obtain ⟨C, hC⟩ := hf
    refine ⟨C, fun q j => ?_⟩
    rw [RealJacquetRadial.mulOp_apply, map_smul, norm_smul]
    have h1 : ‖RealJacquetRadial.sq (radialParam h s₀) a b q‖ ≤ 1 := by
      simp only [RealJacquetRadial.sq, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (show 0 < radialParam h s₀ q a b from Real.exp_pos _)]
      exact pow_le_one₀ (Real.exp_pos _).le (radialParam_lt_one hh hs₀ q hab).le
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hC q j)
  inv_mem a b hab f hf := by
    obtain ⟨C, hC⟩ := hf
    set M := (1 - Real.exp (-s₀) ^ 2)⁻¹ with hM
    have hlt : Real.exp (-s₀) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs₀)
    have hpos : 0 < 1 - Real.exp (-s₀) ^ 2 := by
      have := Real.exp_pos (-s₀)
      nlinarith
    refine ⟨M * C, fun q j => ?_⟩
    rw [RealJacquetRadial.mulOp_apply, map_smul, norm_smul, mul_assoc]
    have hr0 : 0 < radialParam h s₀ q a b := Real.exp_pos _
    have hr1 := radialParam_le hh hs₀ q hab
    have hsq : (1 : ℂ) - RealJacquetRadial.sq (radialParam h s₀) a b q =
        ((1 - radialParam h s₀ q a b ^ 2 : ℝ) : ℂ) := by
      simp [RealJacquetRadial.sq]
    have hnorm : ‖(1 - RealJacquetRadial.sq (radialParam h s₀) a b q)⁻¹‖ ≤ M := by
      rw [hsq, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      have hp2 : 1 - Real.exp (-s₀) ^ 2 ≤ 1 - radialParam h s₀ q a b ^ 2 := by
        have := pow_le_pow_left₀ hr0.le hr1 2
        linarith
      rw [abs_of_pos (hpos.trans_le hp2)]
      exact inv_anti₀ hpos hp2
    calc ‖(1 - RealJacquetRadial.sq (radialParam h s₀) a b q)⁻¹‖ * ‖ℓ q (bΨ j) (f q)‖
        ≤ M * ‖ℓ q (bΨ j) (f q)‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ M * (C * normSum ℓ bB bΨ q) :=
          mul_le_mul_of_nonneg_left (hC q j) (inv_nonneg.mpr hpos.le)

end Radial

/-! ## Box vectors -/

section Box

/-- Under radial stability, `X · u` lies in `S` (as a constant function) for every box vector
`u` and every `X`. -/
theorem constMap_op_mem {Q : Type*} {r : Q → Fin n → Fin n → ℝ}
    (hinf : HasInfinitesimalCharacter π) (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    {F : Submodule ℂ V} (hF : ∀ Y : Mat n, Y.transpose = -Y → ∀ f ∈ F, op π Y f ∈ F)
    {S : Submodule ℂ (Q → V)} (hS : RealJacquetRadial.IsRadialStable π r S)
    (hbox : ∀ u ∈ boxSpace π F, RealJacquetRadial.constMap Q V u ∈ S)
    {u : V} (hu : u ∈ boxSpace π F) (Y : Mat n) :
    RealJacquetRadial.constMap Q V (op π Y u) ∈ S := by
  unfold boxSpace at hu
  refine Submodule.iSup_induction _ (motive := fun u => RealJacquetRadial.constMap Q V (op π Y u) ∈ S)
    hu ?_ ?_ ?_
  · rintro β _ ⟨f, hf, rfl⟩
    obtain ⟨idx, -, hprod⟩ := exists_list_of_monomial (n := n)
      (Finsupp.equivFunOnFinite.symm fun i => ((β i : ℕ)))
    rw [← hprod, ← wordOp_map_D, ← Module.End.mul_apply, ← wordOp_cons]
    exact RealJacquetRadial.radial_finiteness hinf hr hF hS hbox _ hf
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]
    exact add_mem hx hy

end Box

/-! ## Vanishing -/

section Vanishing

theorem span_range_coe_basis {M : Type*} [AddCommGroup M] [Module ℂ M] (B : Submodule ℂ M)
    {ι : Type*} (b : Module.Basis ι ℂ B) :
    B ≤ Submodule.span ℂ (Set.range fun i => (b i : M)) := by
  intro x hx
  have h1 : (⟨x, hx⟩ : B) ∈ Submodule.span ℂ (Set.range b) := b.mem_span _
  have h2 := Submodule.mem_map_of_mem (f := B.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

/-- **Vanishing.** Under the hypotheses of `decay`, if moreover `π` has an infinitesimal
character, `ℓ` has derivative `ℓ s ψ (H v)`, `F` is a finite-dimensional `𝔨`-stable subspace of
`V`, and the span `Ψ` of a finite family `bΨ` is stable under the `R_{ab} - R_{ba}`, then
`ℓ s₀ ψ v = 0` for all `s₀ > 0`, `ψ ∈ Ψ` and `v ∈ F`. -/
theorem eq_zero (hinf : HasInfinitesimalCharacter π) (hh : ∀ a b : Fin n, a < b → h a - h b ≤ -1)
    (hadj : ∀ (s : ℝ) (ψ : P) (v : V) (a b : Fin n),
      ℓ s ψ (op π (E a b) v) = -((Real.exp (s * (h a - h b)) : ℝ) : ℂ) * ℓ s (R a b ψ) v)
    (hderiv : ∀ (ψ : P) (v : V) (s : ℝ),
      HasDerivAt (fun t => ℓ t ψ v) (ℓ s ψ (op π (Matrix.diagonal h) v)) s)
    {c : ℝ} (hgrowth : ∀ (ψ : P) (v : V), ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
      ‖ℓ s ψ v‖ ≤ C * Real.exp (c * s))
    (htop : realJacquetSubspace n π = ⊤)
    {F : Submodule ℂ V} [FiniteDimensional ℂ F]
    (hF : ∀ Y : Mat n, Y.transpose = -Y → ∀ f ∈ F, op π Y f ∈ F)
    {p : ℕ} (bΨ : Fin p → P)
    (hΨ : ∀ a b : Fin n, ∀ ψ ∈ Submodule.span ℂ (Set.range bΨ),
      R a b ψ - R b a ψ ∈ Submodule.span ℂ (Set.range bΨ))
    {s₀ : ℝ} (hs₀ : 0 < s₀) {ψ : P} (hψ : ψ ∈ Submodule.span ℂ (Set.range bΨ)) {v : V}
    (hv : v ∈ F) : ℓ s₀ ψ v = 0 := by
  -- spanning families of the box space and of `Ψ`
  set B := boxSpace π F with hBdef
  let bB0 := Module.finBasis ℂ B
  set m := Module.finrank ℂ B
  let bB : Fin m → V := fun i => (bB0 i : V)
  have hBspan : B ≤ Submodule.span ℂ (Set.range bB) := span_range_coe_basis B bB0
  have hΨspan : Submodule.span ℂ (Set.range bΨ) ≤ Submodule.span ℂ (Set.range bΨ) := le_rfl
  have hbΨ : ∀ j, bΨ j ∈ Submodule.span ℂ (Set.range bΨ) := fun j =>
    Submodule.subset_span ⟨j, rfl⟩
  -- radial finiteness for the bounded space
  have hr : ∀ (q : Set.Ici s₀) (a b : Fin n), a < b → radialParam h s₀ q a b ^ 2 ≠ 1 :=
    fun q a b hab => radialParam_sq_ne_one hh hs₀ q a b hab
  have hS := isRadialStable_boundedSpace (ℓ := ℓ) (bB := bB) hh hs₀ hadj hΨspan hbΨ hΨ
  have hbox : ∀ u ∈ boxSpace π F, RealJacquetRadial.constMap (Set.Ici s₀) V u ∈
      boundedSpace ℓ bB bΨ s₀ := fun u hu => constMap_mem_boundedSpace (hBspan hu)
  obtain ⟨CH, hCH⟩ : ∃ CH : ℝ, ∀ (q : Set.Ici s₀) (i : Fin m) (j : Fin p),
      ‖ℓ q (bΨ j) (op π (Matrix.diagonal h) (bB i))‖ ≤ CH * normSum ℓ bB bΨ q := by
    choose C hC using fun i => constMap_op_mem hinf hr hF hS hbox (bB0 i).2 (Matrix.diagonal h)
    refine ⟨∑ i, |C i|, fun q i j => (hC i q j).trans ?_⟩
    refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (normSum_nonneg ℓ bB bΨ q)
    exact Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  -- the vector of box coefficients and its derivative
  set K : ℝ := |CH| * m * p with hK
  have hK0 : 0 ≤ K := by positivity
  let Φ : ℝ → (Fin m → Fin p → ℂ) := fun t i j => ℓ t (bΨ j) (bB i)
  let Φ' : ℝ → (Fin m → Fin p → ℂ) := fun t i j => ℓ t (bΨ j) (op π (Matrix.diagonal h) (bB i))
  have hΦ : ∀ t, HasDerivAt Φ (Φ' t) t := fun t =>
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hderiv (bΨ j) (bB i) t
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun t => (hΦ t).continuousAt
  have hnormSum : ∀ t, normSum ℓ bB bΨ t ≤ m * p * ‖Φ t‖ := by
    intro t
    unfold normSum
    calc ∑ i, ∑ j, ‖ℓ t (bΨ j) (bB i)‖ ≤ ∑ _i : Fin m, ∑ _j : Fin p, ‖Φ t‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            (norm_le_pi_norm (Φ t i) j).trans (norm_le_pi_norm (Φ t) i)
      _ = m * p * ‖Φ t‖ := by simp [Finset.sum_const, Finset.card_univ, mul_assoc]
  have hbound : ∀ t, s₀ ≤ t → ‖Φ' t‖ ≤ K * ‖Φ t‖ := by
    intro t ht
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    calc ‖Φ' t i j‖ ≤ CH * normSum ℓ bB bΨ t := hCH ⟨t, ht⟩ i j
      _ ≤ |CH| * normSum ℓ bB bΨ t :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (normSum_nonneg ℓ bB bΨ t)
      _ ≤ |CH| * (m * p * ‖Φ t‖) := mul_le_mul_of_nonneg_left (hnormSum t) (abs_nonneg _)
      _ = K * ‖Φ t‖ := by rw [hK]; ring
  -- Gronwall backwards from `T` to `s₀`
  have hgron : ∀ T, s₀ ≤ T → ‖Φ s₀‖ ≤ ‖Φ T‖ * Real.exp (K * (T - s₀)) := by
    intro T hT
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun u => Φ (s₀ + T - u))
      (f' := fun u => -Φ' (s₀ + T - u)) (δ := ‖Φ T‖) (K := K) (ε := 0) (a := s₀) (b := T)
      (hΦc.comp (continuous_const.sub continuous_id)).continuousOn
      (fun u _ => (HasDerivAt.comp_const_sub (s₀ + T) u (hΦ (s₀ + T - u))).hasDerivWithinAt)
      (by simp) (fun u hu => by
        rw [norm_neg, add_zero]
        exact hbound _ (by linarith [hu.2]))
      T ⟨hT, le_rfl⟩
    simpa [gronwallBound_ε0] using this
  -- decay of the box coefficients
  obtain ⟨k, hk⟩ := exists_nat_gt (c + K + 1)
  have hdec := decay hh hadj hgrowth htop k
  choose Cd hCd using fun (i : Fin m) (j : Fin p) =>
    (hdec ▸ Submodule.mem_top : bB i ∈ decaySpace ℓ c k) (bΨ j)
  set A : ℝ := ∑ i, ∑ j, |Cd i j| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΦT : ∀ T, s₀ ≤ T → ‖Φ T‖ ≤ A * Real.exp ((c - k) * T) := by
    intro T hT
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have hle : |Cd i j| ≤ A :=
      (Finset.single_le_sum (f := fun j' => |Cd i j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i' => ∑ j', |Cd i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    calc ‖Φ T i j‖ ≤ Cd i j * Real.exp ((c - k) * T) := hCd i j T (by linarith)
      _ ≤ |Cd i j| * Real.exp ((c - k) * T) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ A * Real.exp ((c - k) * T) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  have hfinal : ∀ T, s₀ ≤ T → ‖Φ s₀‖ ≤ A * Real.exp (-(K * s₀)) * Real.exp (-T) := by
    intro T hT
    calc ‖Φ s₀‖ ≤ ‖Φ T‖ * Real.exp (K * (T - s₀)) := hgron T hT
      _ ≤ A * Real.exp ((c - k) * T) * Real.exp (K * (T - s₀)) :=
          mul_le_mul_of_nonneg_right (hΦT T hT) (Real.exp_pos _).le
      _ = A * Real.exp (-(K * s₀)) * Real.exp ((c - k + K) * T) := by
          have e : Real.exp ((c - k) * T) * Real.exp (K * (T - s₀)) =
              Real.exp (-(K * s₀)) * Real.exp ((c - k + K) * T) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          rw [mul_assoc, e, ← mul_assoc]
      _ ≤ A * Real.exp (-(K * s₀)) * Real.exp (-T) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith
  have hlim : Filter.Tendsto (fun T => A * Real.exp (-(K * s₀)) * Real.exp (-T)) Filter.atTop
      (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Real.exp (-(K * s₀)))
  have hΦ0 : ‖Φ s₀‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨s₀, hfinal⟩)
  have hz : ∀ i j, ℓ s₀ (bΨ j) (bB i) = 0 := fun i j =>
    congrFun (congrFun (norm_le_zero_iff.mp hΦ0) i) j
  -- conclusion
  obtain ⟨cv, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hBspan (RealJacquetFiniteGeneration.le_boxSpace π F hv))
  obtain ⟨cψ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hΨspan hψ)
  simp [map_sum, map_smul, hz]

end Vanishing

end RealJacquetGronwall

end Langlands.Archimedean
