import Langlands.Representation.Archimedean.RealSubquotientFinite
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-!
# Averaging over `O(n)` and the lifting of intertwiners

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).

* `continuous_apply_envMap`: `k ↦ λ(Ad(k) u)` is continuous for every `u ∈ U(𝔤)` and every linear
  functional `λ`.
* `kstar`: the action `c ↦ τ(k⁻¹)ᵀ Ad(k)(c) τ(k)ᵀ` of `O(n)` on matrices over `U(𝔤)`; its fixed
  points are the `K`-invariant matrices.
* `avg`, `act_avg`, `avg_mem_Bsub` (**averaging**): if `c · γ = γ'` for `K`-intertwiners `γ`,
  `γ'`, then the Haar average `avg τ c` of `c` is `K`-invariant and `avg τ c · γ = γ'`, in every
  module at once.
* `exists_act_eq_of_irreducible` (**simplicity**): in an irreducible module, every linear map
  `T' : ℂ^d → V` is `c · T` for any nonzero `K`-intertwiner `T`.
* `exists_single_kill` (**reduction to one principal series**): if the `K`-invariant matrices
  killing finitely many intertwiners `ω_i` kill a cyclic `T₀ ≠ 0`, then for one `i` and some
  `K`-invariant `c`, the matrices killing `c · ω_i` kill `T₀`.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

open Kostant MvPolynomial Langlands.Algebra.UniversalEnveloping InfinitesimalCharacter

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ## Continuity of the adjoint action -/

/-- `Ad(k) x` is a combination of the `1 ⊗ E_pq` with continuous coefficients. -/
theorem exists_continuous_conjLie (x : LL n) :
    ∃ f : Fin n → Fin n → Matrix.unitaryGroup (Fin n) ℝ → ℂ, (∀ p q, Continuous (f p q)) ∧
      ∀ k, conjLie (orthUnit k) x =
        ∑ p, ∑ q, f p q k • ((1 : ℂ) ⊗ₜ Matrix.single p q (1 : ℝ)) := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    refine ⟨fun p q k => z * (((k : Matrix (Fin n) (Fin n) ℝ) * X *
      (star k : Matrix (Fin n) (Fin n) ℝ)) p q : ℂ), fun p q => ?_, fun k => ?_⟩
    · have hk : Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ =>
          (k : Matrix (Fin n) (Fin n) ℝ) * X * (star k : Matrix (Fin n) (Fin n) ℝ) :=
        (continuous_subtype_val.mul continuous_const).mul
          (continuous_star.comp continuous_subtype_val)
      exact continuous_const.mul (Complex.continuous_ofReal.comp (hk.matrix_elem p q))
    · rw [conjLie_tmul]
      set Y := (k : Matrix (Fin n) (Fin n) ℝ) * X * (star k : Matrix (Fin n) (Fin n) ℝ)
      have hY : ∀ p q, (z * ((Y p q : ℝ) : ℂ)) • ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single p q (1 : ℝ)) =
          z ⊗ₜ[ℝ] Matrix.single p q (Y p q) := by
        intro p q
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          show Matrix.single p q (Y p q) = Y p q • Matrix.single p q (1 : ℝ) by
            rw [Matrix.smul_single, smul_eq_mul, mul_one],
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', Complex.real_smul, mul_comm]
      show z ⊗ₜ[ℝ] Y = ∑ p, ∑ q, (z * ((Y p q : ℝ) : ℂ)) •
        ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single p q (1 : ℝ))
      rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hY p q]
      simp only [← TensorProduct.tmul_sum]
      rw [← Matrix.matrix_eq_sum_single]
  | add x y hx hy =>
    obtain ⟨f, hf, hfx⟩ := hx
    obtain ⟨g, hg, hgy⟩ := hy
    refine ⟨fun p q k => f p q k + g p q k, fun p q => (hf p q).add (hg p q), fun k => ?_⟩
    rw [map_add, hfx k, hgy k, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [add_smul]

/-- **Continuity of the adjoint action.** `k ↦ Λ(Ad(k) u)` is continuous. -/
theorem continuous_apply_envMap (u : UU n) (Λ : UU n →ₗ[ℂ] ℂ) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ => Λ (envMap (conjLie (orthUnit k)) u) := by
  have hword : ∀ (l : List (LL n)) (Λ : UU n →ₗ[ℂ] ℂ), Continuous fun k :
      Matrix.unitaryGroup (Fin n) ℝ => Λ (envMap (conjLie (orthUnit k)) (word ℂ (LL n) l)) := by
    intro l
    induction l with
    | nil => intro Λ; simp only [word_nil, map_one]; exact continuous_const
    | cons x l ih =>
      intro Λ
      obtain ⟨f, hf, hfx⟩ := exists_continuous_conjLie x
      have h : ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
          Λ (envMap (conjLie (orthUnit k)) (word ℂ (LL n) (x :: l))) =
            ∑ p, ∑ q, f p q k * (Λ ∘ₗ LinearMap.mulLeft ℂ (UniversalEnvelopingAlgebra.ι ℂ
              ((1 : ℂ) ⊗ₜ Matrix.single p q (1 : ℝ)))) (envMap (conjLie (orthUnit k))
                (word ℂ (LL n) l)) := by
        intro k
        rw [word_cons, map_mul, envMap_ι, hfx k, map_sum, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [map_sum, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, smul_mul_assoc, map_smul, smul_eq_mul]
        rfl
      simp only [h]
      exact continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
        (hf p q).mul (ih _)
  obtain ⟨N, hN⟩ := exists_mem_degreeFiltration ℂ (LL n) u
  have hu := degreeFiltration_le_wordSpan ℂ (LL n) N hN
  clear hN
  induction hu using Submodule.span_induction with
  | mem w hw => obtain ⟨l, -, rfl⟩ := hw; exact hword l Λ
  | zero => simp only [map_zero]; exact continuous_const
  | add w w' _ _ h h' => simp only [map_add]; exact h.add h'
  | smul c w _ h => simp only [map_smul, smul_eq_mul]; exact continuous_const.mul h

/-! ## The action of `O(n)` on matrices over `U(𝔤)` -/

/-- `Ad(k)` on `U(𝔤)`. -/
abbrev AdU (k : Matrix.unitaryGroup (Fin n) ℝ) : UU n →ₐ[ℂ] UU n := envMap (conjLie (orthUnit k))

theorem orthUnit_mul (k k' : Matrix.unitaryGroup (Fin n) ℝ) :
    orthUnit (k * k') = orthUnit k * orthUnit k' := by
  apply Units.ext
  rw [Units.val_mul, orthUnit_val, orthUnit_val, orthUnit_val, ← map_mul]
  rfl

theorem AdU_mul (k k' : Matrix.unitaryGroup (Fin n) ℝ) (u : UU n) :
    AdU (k * k') u = AdU k (AdU k' u) := by
  rw [AdU, orthUnit_mul, conjLie_mul, envMap_comp]
  rfl

section Kstar

variable {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)

/-- `k ⋆ c = τ(k⁻¹)ᵀ Ad(k)(c) τ(k)ᵀ`. -/
def kstar (k : Matrix.unitaryGroup (Fin n) ℝ) (c : Matrix (Fin d) (Fin d) (UU n)) :
    Matrix (Fin d) (Fin d) (UU n) :=
  (τ k⁻¹)ᵀ.map (algebraMap ℂ (UU n)) * c.map (AdU k) * (τ k)ᵀ.map (algebraMap ℂ (UU n))

theorem scal_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    A.map (algebraMap ℂ (UU n)) * B.map (algebraMap ℂ (UU n)) =
      (A * B).map (algebraMap ℂ (UU n)) :=
  (Matrix.map_mul (f := algebraMap ℂ (UU n))).symm

theorem scal_map_AdU (A : Matrix (Fin d) (Fin d) ℂ) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (A.map (algebraMap ℂ (UU n))).map (AdU k) = A.map (algebraMap ℂ (UU n)) := by
  ext i j
  simp

theorem map_AdU_mul (A B : Matrix (Fin d) (Fin d) (UU n)) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (A * B).map (AdU k) = A.map (AdU k) * B.map (AdU k) :=
  Matrix.map_mul (f := (AdU k).toRingHom)

theorem kstar_mul (k k' : Matrix.unitaryGroup (Fin n) ℝ) (c : Matrix (Fin d) (Fin d) (UU n)) :
    kstar τ (k * k') c = kstar τ k (kstar τ k' c) := by
  have hmap : c.map (AdU (k * k')) = (c.map (AdU k')).map (AdU k) := by
    ext i j; simp [AdU_mul]
  simp only [kstar, map_AdU_mul, scal_map_AdU, hmap]
  rw [mul_inv_rev, map_mul, map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← scal_mul,
    ← scal_mul]
  simp only [Matrix.mul_assoc]

theorem kstar_add (k : Matrix.unitaryGroup (Fin n) ℝ) (c c' : Matrix (Fin d) (Fin d) (UU n)) :
    kstar τ k (c + c') = kstar τ k c + kstar τ k c' := by
  simp only [kstar, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem kstar_smul (k : Matrix.unitaryGroup (Fin n) ℝ) (r : ℂ) (c : Matrix (Fin d) (Fin d) (UU n)) :
    kstar τ k (r • c) = r • kstar τ k c := by
  simp only [kstar]
  rw [show (r • c).map (AdU k) = r • c.map (AdU k) by ext i j; simp, Matrix.mul_smul,
    Matrix.smul_mul]

theorem kstar_apply (k : Matrix.unitaryGroup (Fin n) ℝ) (c : Matrix (Fin d) (Fin d) (UU n))
    (i j : Fin d) :
    kstar τ k c i j = ∑ b, ∑ a, (τ k⁻¹ a i * τ k j b) • AdU k (c a b) := by
  have hc : ∀ (x y : ℂ) (u : UU n),
      algebraMap ℂ (UU n) x * u * algebraMap ℂ (UU n) y = (x * y) • u := by
    intro x y u
    rw [Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes y u, ← mul_assoc]
  simp only [kstar, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  exact hc _ _ _

/-- Matrices fixed by every `k ⋆ ·` are `K`-invariant. -/
theorem mem_Bsub_of_kstar {b : Matrix (Fin d) (Fin d) (UU n)} (hb : ∀ k, kstar τ k b = b) :
    b ∈ Bsub τ := by
  intro k
  calc (τ k)ᵀ.map (algebraMap ℂ (UU n)) * b = (τ k)ᵀ.map (algebraMap ℂ (UU n)) * kstar τ k b := by
        rw [hb k]
    _ = b.map (envMap (conjLie (orthUnit k))) * (τ k)ᵀ.map (algebraMap ℂ (UU n)) := by
      rw [kstar, ← Matrix.mul_assoc, ← Matrix.mul_assoc, scal_mul, ← Matrix.transpose_mul,
        ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

/-- `k ⋆ c` acts on `K`-intertwiners like `c`. -/
theorem act_kstar {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M} (P : UU n →ₐ[ℂ] Module.End ℂ M)
    (hρP : ∀ k u, ρ k * P u = P (AdU k u) * ρ k) {c : Matrix (Fin d) (Fin d) (UU n)}
    {γ γ' : (Fin d → ℂ) →ₗ[ℂ] M} (hγ : γ ∈ gkIntertwiners ρ d τ)
    (hγ' : γ' ∈ gkIntertwiners ρ d τ) (hc : act P c γ = γ') (k : Matrix.unitaryGroup (Fin n) ℝ) :
    act P (kstar τ k c) γ = γ' := by
  have hcomm : ∀ (T : (Fin d → ℂ) →ₗ[ℂ] M), T ∈ gkIntertwiners ρ d τ →
      ρ k ∘ₗ T = act P ((τ k)ᵀ.map (algebraMap ℂ (UU n))) T := by
    intro T hT
    rw [act_scalar, Matrix.transpose_transpose]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, hT k y]
  have h1 : act P (c.map (AdU k) * (τ k)ᵀ.map (algebraMap ℂ (UU n))) γ =
      act P ((τ k)ᵀ.map (algebraMap ℂ (UU n))) γ' := by
    rw [act_mul, ← hcomm γ hγ, ← comp_act P (ρ k) _ (fun u => hρP k u), hc, hcomm γ' hγ']
  rw [kstar, Matrix.mul_assoc, act_mul, h1, ← act_mul, scal_mul, ← Matrix.transpose_mul,
    ← map_mul, mul_inv_cancel, map_one, Matrix.transpose_one, act_scalar, Matrix.transpose_one,
    Matrix.toLin'_one, LinearMap.comp_id]

/-- `Ad(k)` preserves the filtration. -/
theorem AdU_mem_degreeFiltration (k : Matrix.unitaryGroup (Fin n) ℝ) {N : ℕ} {u : UU n}
    (hu : u ∈ degreeFiltration ℂ (LL n) N) : AdU k u ∈ degreeFiltration ℂ (LL n) N :=
  algHom_mem_degreeFiltration ℂ (LL n) (LL n) _ (fun x => by
    rw [envMap_ι]; exact generator_mem_degreeOne ℂ (LL n) _) hu

theorem kstar_mem {N : ℕ} {c : Matrix (Fin d) (Fin d) (UU n)}
    (hc : ∀ i j, c i j ∈ degreeFiltration ℂ (LL n) N) (k : Matrix.unitaryGroup (Fin n) ℝ)
    (i j : Fin d) : kstar τ k c i j ∈ degreeFiltration ℂ (LL n) N := by
  rw [kstar_apply]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (AdU_mem_degreeFiltration k (hc a b))

/-- Continuity of `k ↦ Λ(k ⋆ c)`. -/
theorem continuous_apply_kstar (hτ : Continuous τ) (c : Matrix (Fin d) (Fin d) (UU n))
    (Λ : Matrix (Fin d) (Fin d) (UU n) →ₗ[ℂ] ℂ) :
    Continuous fun k => Λ (kstar τ k c) := by
  classical
  let Λij : Fin d → Fin d → UU n →ₗ[ℂ] ℂ := fun i j =>
    Λ ∘ₗ { toFun := fun u => Matrix.single i j u
           map_add' := fun u v => Matrix.single_add i j u v
           map_smul' := fun r u => (Matrix.smul_single r i j u).symm }
  have hΛ : ∀ k, Λ (kstar τ k c) = ∑ i, ∑ j, ∑ b, ∑ a,
      (τ k⁻¹ a i * τ k j b) * Λij i j (AdU k (c a b)) := by
    intro k
    conv_lhs => rw [Matrix.matrix_eq_sum_single (kstar τ k c)]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Λ (Matrix.single i j (kstar τ k c i j)) = Λij i j (kstar τ k c i j) := rfl
    rw [this, kstar_apply]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [hΛ]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun a _ => ?_
  refine ((((hτ.comp continuous_inv).matrix_elem a i).mul (hτ.matrix_elem j b))).mul ?_
  exact continuous_apply_envMap (c a b) (Λij i j)

end Kstar

/-! ## The Haar average -/

theorem act_smul {d : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (P : UU n →ₐ[ℂ] Module.End ℂ M) (r : ℂ) (b : Matrix (Fin d) (Fin d) (UU n))
    (T : (Fin d → ℂ) →ₗ[ℂ] M) : act P (r • b) T = r • act P b T := by
  refine LinearMap.pi_ext fun i c => ?_
  simp [act_single, Finset.smul_sum, smul_comm r c]

/-- Matrices with entries in `U_N`. -/
def matW (d N : ℕ) : Submodule ℂ (Matrix (Fin d) (Fin d) (UU n)) where
  carrier := {b | ∀ i j, b i j ∈ degreeFiltration ℂ (LL n) N}
  add_mem' ha hb i j := Submodule.add_mem _ (ha i j) (hb i j)
  zero_mem' _ _ := Submodule.zero_mem _
  smul_mem' c _ hb i j := Submodule.smul_mem _ c (hb i j)

instance finiteDimensional_matW (d N : ℕ) : FiniteDimensional ℂ (matW (n := n) d N) := by
  have : Module.Finite ℂ (degreeFiltration ℂ (LL n) N) :=
    Module.Finite.iff_fg.2 (degreeFiltration_fg ℂ (LL n) N)
  let f : matW (n := n) d N →ₗ[ℂ] (Fin d → Fin d → degreeFiltration ℂ (LL n) N) :=
    { toFun := fun b => fun i' j' => ⟨(b : Matrix (Fin d) (Fin d) (UU n)) i' j', b.2 i' j'⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun b b' h => ?_
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h i) j
  exact congrArg Subtype.val this

theorem exists_level {d : ℕ} (c : Matrix (Fin d) (Fin d) (UU n)) :
    ∃ N, ∀ i j, c i j ∈ degreeFiltration ℂ (LL n) N := by
  classical
  choose f hf using fun ij : Fin d × Fin d => exists_mem_degreeFiltration ℂ (LL n) (c ij.1 ij.2)
  exact ⟨Finset.univ.sup f, fun i j =>
    degreeFiltration_mono ℂ (LL n) (Finset.le_sup (Finset.mem_univ (i, j))) (hf (i, j))⟩

/-- The normalized Haar measure on `O(n)` (up to the factor `μ(O(n))`). -/
abbrev haarO (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℝ) := Measure.haar

instance isFiniteMeasure_haarO (n : ℕ) : IsFiniteMeasure (haarO n) :=
  ⟨isCompact_univ.measure_lt_top⟩

section Avg

variable {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)

/-- The coordinate functionals of a basis of `matW d N`, extended to all matrices. -/
def coordExt (N : ℕ) (i : Fin (Module.finrank ℂ (matW (n := n) d N))) :
    Matrix (Fin d) (Fin d) (UU n) →ₗ[ℂ] ℂ :=
  Classical.choose (LinearMap.exists_extend ((Module.finBasis ℂ (matW (n := n) d N)).coord i))

theorem coordExt_apply (N : ℕ) (i : Fin (Module.finrank ℂ (matW (n := n) d N)))
    (w : matW (n := n) d N) :
    coordExt (d := d) N i (w : Matrix (Fin d) (Fin d) (UU n)) =
      (Module.finBasis ℂ (matW (n := n) d N)).repr w i := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend ((Module.finBasis ℂ (matW (n := n) d N)).coord i))
  have := LinearMap.congr_fun h w
  simpa [coordExt] using this

theorem eq_sum_coordExt (N : ℕ) {w : Matrix (Fin d) (Fin d) (UU n)} (hw : w ∈ matW (n := n) d N) :
    w = ∑ i, coordExt N i w • ((Module.finBasis ℂ (matW (n := n) d N) i : matW (n := n) d N) :
      Matrix (Fin d) (Fin d) (UU n)) := by
  have h := (Module.finBasis ℂ (matW (n := n) d N)).sum_repr ⟨w, hw⟩
  have h2 := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordExt_apply N i ⟨w, hw⟩]

/-- The Haar average of `c` under `k ⋆ ·`. -/
def avg (c : Matrix (Fin d) (Fin d) (UU n)) : Matrix (Fin d) (Fin d) (UU n) :=
  (((haarO n).real Set.univ : ℂ))⁻¹ • ∑ i, (∫ k, coordExt (exists_level c).choose i (kstar τ k c)
    ∂haarO n) • ((Module.finBasis ℂ (matW (n := n) d (exists_level c).choose) i :
      matW (n := n) d (exists_level c).choose) : Matrix (Fin d) (Fin d) (UU n))

variable {τ}

/-- Every linear functional of the average is the average of the functional. -/
theorem apply_avg (hτ : Continuous τ) (c : Matrix (Fin d) (Fin d) (UU n))
    (Φ : Matrix (Fin d) (Fin d) (UU n) →ₗ[ℂ] ℂ) :
    Φ (avg τ c) = (((haarO n).real Set.univ : ℂ))⁻¹ * ∫ k, Φ (kstar τ k c) ∂haarO n := by
  rw [avg]
  set N := (exists_level c).choose with hNdef
  have hN : ∀ i j, c i j ∈ degreeFiltration ℂ (LL n) N := (exists_level c).choose_spec
  have hexp : ∀ k, Φ (kstar τ k c) =
      ∑ i, coordExt N i (kstar τ k c) * Φ ((Module.finBasis ℂ (matW (n := n) d N) i :
        matW (n := n) d N) : Matrix (Fin d) (Fin d) (UU n)) := by
    intro k
    conv_lhs => rw [eq_sum_coordExt N (show kstar τ k c ∈ matW (n := n) d N from
      fun i j => kstar_mem τ hN k i j)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun k => coordExt N i (kstar τ k c) *
      Φ ((Module.finBasis ℂ (matW (n := n) d N) i : matW (n := n) d N) :
        Matrix (Fin d) (Fin d) (UU n))) (haarO n) := fun i =>
    OrthogonalFinitePolynomial.integrable_of_continuous (haarO n)
      ((continuous_apply_kstar τ hτ c _).mul continuous_const)
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => hint i, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, integral_mul_const]

/-- **Averaging.** If `c · γ = γ'` for `K`-intertwiners `γ`, `γ'` (in any module with
`ρ(k) P(u) = P(Ad(k) u) ρ(k)`), then `avg c · γ = γ'`. -/
theorem act_avg (hτ : Continuous τ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M} (P : UU n →ₐ[ℂ] Module.End ℂ M)
    (hρP : ∀ k u, ρ k * P u = P (AdU k u) * ρ k) {c : Matrix (Fin d) (Fin d) (UU n)}
    {γ γ' : (Fin d → ℂ) →ₗ[ℂ] M} (hγ : γ ∈ gkIntertwiners ρ d τ)
    (hγ' : γ' ∈ gkIntertwiners ρ d τ) (hc : act P c γ = γ') : act P (avg τ c) γ = γ' := by
  refine LinearMap.ext fun x => ?_
  rw [← sub_eq_zero]
  refine (_root_.Module.forall_dual_apply_eq_zero_iff ℂ (act P (avg τ c) γ x - γ' x)).mp
    fun ℓ => ?_
  let Φ : Matrix (Fin d) (Fin d) (UU n) →ₗ[ℂ] ℂ :=
    { toFun := fun b => ℓ (act P b γ x)
      map_add' := fun b b' => by rw [act_add, LinearMap.add_apply, map_add]
      map_smul' := fun r b => by rw [act_smul, LinearMap.smul_apply, map_smul]; rfl }
  have h1 := apply_avg hτ c Φ
  have h2 : ∀ k, Φ (kstar τ k c) = ℓ (γ' x) := fun k => by
    change ℓ (act P (kstar τ k c) γ x) = _
    rw [act_kstar τ P hρP hγ hγ' hc k]
  simp only [h2, integral_const] at h1
  change ℓ (act P (avg τ c) γ x) = _ at h1
  rw [map_sub, h1, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero), one_mul, sub_self]

/-- **The average is `K`-invariant.** -/
theorem avg_mem_Bsub (hτ : Continuous τ) (c : Matrix (Fin d) (Fin d) (UU n)) :
    avg τ c ∈ Bsub τ := by
  refine mem_Bsub_of_kstar τ fun k' => ?_
  rw [← sub_eq_zero]
  refine (_root_.Module.forall_dual_apply_eq_zero_iff ℂ (kstar τ k' (avg τ c) - avg τ c)).mp
    fun Φ => ?_
  let Ψ : Matrix (Fin d) (Fin d) (UU n) →ₗ[ℂ] ℂ :=
    { toFun := fun b => Φ (kstar τ k' b)
      map_add' := fun b b' => by rw [kstar_add, map_add]
      map_smul' := fun r b => by rw [kstar_smul, map_smul]; rfl }
  have h1 := apply_avg hτ c Ψ
  change Φ (kstar τ k' (avg τ c)) = _ at h1
  have h2 : ∀ k, Ψ (kstar τ k c) = Φ (kstar τ (k' * k) c) := fun k => by
    change Φ (kstar τ k' (kstar τ k c)) = _
    rw [kstar_mul]
  simp only [h2] at h1
  rw [integral_mul_left_eq_self (fun k => Φ (kstar τ k c)) k'] at h1
  rw [map_sub, h1, apply_avg hτ c Φ, sub_self]

end Avg

/-! ## Simplicity and the reduction to one principal series -/

section Simple

variable {d : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (P : UU n →ₐ[ℂ] Module.End ℂ M)

theorem act_one (T : (Fin d → ℂ) →ₗ[ℂ] M) : act P (1 : Matrix (Fin d) (Fin d) (UU n)) T = T := by
  have h := act_scalar P (1 : Matrix (Fin d) (Fin d) ℂ) T
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.toLin'_one,
    LinearMap.comp_id] at h
  exact h

theorem act_zero_right (b : Matrix (Fin d) (Fin d) (UU n)) :
    act P b (0 : (Fin d → ℂ) →ₗ[ℂ] M) = 0 := by
  refine LinearMap.pi_ext fun i c => ?_
  simp [act_single]

theorem PhiT_apply (T : (Fin d → ℂ) →ₗ[ℂ] M) (w : Fin d → UU n) :
    PhiT P T w = ∑ j, P (w j) (T (Pi.single j 1)) := rfl

theorem apply_mem_range_PhiT (T : (Fin d → ℂ) →ₗ[ℂ] M) (u : UU n) (x : Fin d → ℂ) :
    P u (T x) ∈ LinearMap.range (PhiT P T) := by
  refine ⟨fun j => x j • u, ?_⟩
  rw [PhiT_apply, apply_eq_sum_single T x, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  rfl

end Simple

/-- **Simplicity.** In an irreducible `(𝔤𝔩_n(ℝ), O(n))`-module, every linear map `T' : ℂ^d → V`
is `c · T` for every nonzero `K`-intertwiner `T` from `τ`. -/
theorem exists_act_eq_of_irreducible {d : ℕ}
    {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ} {M : Type*} [AddCommGroup M]
    [Module ℂ M] {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ M} (hgk : IsRealGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) {T T' : (Fin d → ℂ) →ₗ[ℂ] M}
    (hT : T ∈ gkIntertwiners ρ d τ) (hT0 : T ≠ 0) :
    ∃ c : Matrix (Fin d) (Fin d) (UU n), act (envelopingAction π) c T = T' := by
  classical
  set P := envelopingAction π
  set R := LinearMap.range (PhiT P T)
  have hρP : ∀ k u, ρ k * P u = P (AdU k u) * ρ k := fun k u =>
    rho_mul_envelopingAction hgk.2.2.2 k u
  have hρ : ∀ k, ∀ v ∈ R, ρ k v ∈ R := by
    rintro k _ ⟨w, rfl⟩
    rw [PhiT_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Module.End.mul_apply, hρP, Module.End.mul_apply, ← hT k (Pi.single j 1)]
    exact apply_mem_range_PhiT P T _ _
  have hπ : ∀ X, ∀ v ∈ R, π X v ∈ R := by
    rintro X _ ⟨w, rfl⟩
    rw [PhiT_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : π X (P (w j) (T (Pi.single j 1))) =
        P (UniversalEnvelopingAlgebra.ι ℂ X * w j) (T (Pi.single j 1)) := by
      rw [map_mul, Module.End.mul_apply]
      simp [P, envelopingAction]
    rw [this]
    exact apply_mem_range_PhiT P T _ _
  have hR : R = ⊤ := by
    rcases hirr.2 R hρ hπ with h | h
    · exfalso
      apply hT0
      refine LinearMap.ext fun x => ?_
      have : T x ∈ R := by
        have := apply_mem_range_PhiT P T 1 x
        rwa [map_one, Module.End.one_apply] at this
      rw [h] at this
      simpa using this
    · exact h
  have hmem : ∀ i, ∃ w : Fin d → UU n, PhiT P T w = T' (Pi.single i 1) := fun i => by
    have : T' (Pi.single i 1) ∈ R := by rw [hR]; trivial
    exact this
  choose w hw using hmem
  refine ⟨Matrix.of fun i j => w i j, LinearMap.pi_ext fun i c => ?_⟩
  rw [act_single]
  simp only [Matrix.of_apply]
  rw [← PhiT_apply, hw i, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Reduction to one principal series.** Let `T₀ ≠ 0` be cyclic for the `K`-invariant
matrices, and let every `K`-invariant `b` killing all the `ω_i`, `i ∈ F`, kill `T₀`. Then
there are a single `i ∈ F` and a `K`-invariant `c` such that every `K`-invariant `b` killing
`c · ω_i` kills `T₀`. -/
theorem exists_single_kill {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {ι : Type*} (F : Finset ι) {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module ℂ (Ms i)]
    (P : ∀ i, UU n →ₐ[ℂ] Module.End ℂ (Ms i)) (ω : ∀ i, (Fin d → ℂ) →ₗ[ℂ] Ms i)
    {MV : Type*} [AddCommGroup MV] [Module ℂ MV] (PV : UU n →ₐ[ℂ] Module.End ℂ MV)
    (T0 : (Fin d → ℂ) →ₗ[ℂ] MV) (hT0 : T0 ≠ 0)
    (hkill : ∀ b ∈ Bsub τ, (∀ i ∈ F, act (P i) b (ω i) = 0) → act PV b T0 = 0)
    (hsimple : ∀ b ∈ Bsub τ, act PV b T0 ≠ 0 → ∃ b' ∈ Bsub τ, act PV (b' * b) T0 = T0) :
    ∃ i ∈ F, ∃ c ∈ Bsub τ, ∀ b ∈ Bsub τ,
      act (P i) b (act (P i) c (ω i)) = 0 → act PV b T0 = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exfalso
    have := hkill 1 (Subalgebra.one_mem _) (by simp)
    rw [act_one] at this
    exact hT0 this
  | insert f0 F' hf0 ih =>
    by_cases hA : ∃ c ∈ Bsub τ, (∀ g ∈ F', act (P g) c (ω g) = 0) ∧ act PV c T0 ≠ 0
    · obtain ⟨c, hc, hcF, hcT⟩ := hA
      obtain ⟨b', hb', hb'c⟩ := hsimple c hc hcT
      refine ⟨f0, Finset.mem_insert_self _ _, b' * c, Subalgebra.mul_mem _ hb' hc,
        fun b hb hbk => ?_⟩
      have h1 : act PV (b * (b' * c)) T0 = 0 := by
        refine hkill _ (Subalgebra.mul_mem _ hb (Subalgebra.mul_mem _ hb' hc)) fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [act_mul]; exact hbk
        · rw [← mul_assoc, act_mul, hcF i hi, act_zero_right]
      rw [act_mul, hb'c] at h1
      exact h1
    · push Not at hA
      obtain ⟨i, hi, c, hc, hic⟩ := ih hA
      exact ⟨i, Finset.mem_insert_of_mem hi, c, hc, hic⟩

end RealSubquotient

end Langlands.Archimedean
