import Langlands.Representation.Archimedean.RealSubquotientAverage

/-!
# A `K`-type of a `(𝔤𝔩_n(ℝ), O(n))`-module as matrix data

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).
For a nonzero vector `v₀` of a `(𝔤𝔩_n(ℝ), O(n))`-module, the span `F₀` of `ρ(O(n)) v₀` is
finite-dimensional; a basis of `F₀` gives a continuous matrix representation `τ` of `O(n)`, its
derivative `D` (`IsTypeDerivative`) and the nonzero `K`-intertwiner `T₀ : ℂ^d → V`, the inclusion
of `F₀` (`exists_ktype`).
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The derivative at `0` of a curve in `O(n)` through `1` is antisymmetric. -/
theorem transpose_eq_neg_of_curve {γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (h0 : γ 0 = 1)
    (hX : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j) (X i j) 0) :
    Xᵀ = -X := by
  ext i j
  have hconst : (fun t => ∑ m, (γ t : Matrix (Fin n) (Fin n) ℝ) m j *
      (γ t : Matrix (Fin n) (Fin n) ℝ) m i) = fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) j i := by
    funext t
    have := Matrix.mem_unitaryGroup_iff'.mp (γ t).2
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.transpose_apply]
  have hd : HasDerivAt (fun t => ∑ m, (γ t : Matrix (Fin n) (Fin n) ℝ) m j *
      (γ t : Matrix (Fin n) (Fin n) ℝ) m i)
      (∑ m, (X m j * (γ 0 : Matrix (Fin n) (Fin n) ℝ) m i +
        (γ 0 : Matrix (Fin n) (Fin n) ℝ) m j * X m i)) 0 := by
    apply HasDerivAt.fun_sum
    intro m _
    exact (hX m j).mul (hX m i)
  rw [hconst] at hd
  have h := hd.unique (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℝ) j i))
  rw [h0] at h
  simp only [OneMemClass.coe_one, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

/-- The skew part of an antisymmetric matrix is the matrix. -/
theorem skewPart_eq_self {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Yᵀ = -Y) :
    RealJacquetFrobenius.skewPart Y = Y := by
  ext i j
  have hij : Y j i = -Y i j := by
    have := congrFun (congrFun hY i) j
    simpa using this
  rw [RealJacquetFrobenius.skewPart_apply]
  rcases lt_trichotomy j i with h | h | h
  · simp [h]
  · subst h
    have : Y j j = 0 := by linarith [hij]
    simp [this]
  · simp [h, not_lt.mpr h.le, hij]

/-- **A `K`-type as matrix data.** A nonzero `(𝔤𝔩_n(ℝ), O(n))`-module has a continuous matrix
representation `τ` of `O(n)` with derivative `D` and a nonzero `K`-intertwiner `T₀` from `τ`. -/
theorem exists_ktype {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} (hgk : IsRealGKModule n ρ π)
    [Nontrivial V] :
    ∃ (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
      (D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ)
      (T0 : (Fin d → ℂ) →ₗ[ℂ] V),
      Continuous τ ∧ IsTypeDerivative τ D ∧ T0 ∈ gkIntertwiners ρ d τ ∧ T0 ≠ 0 ∧ 0 < d := by
  classical
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  set F0 := FiniteVectors.orbitSpan ρ v0 with hF0def
  have : FiniteDimensional ℂ F0 := hgk.1 v0
  have hF0 : ∀ k, ∀ x ∈ F0, ρ k x ∈ F0 := fun k x hx =>
    (FiniteVectors.orbitSubrepresentation ρ v0).apply_mem_toSubmodule k hx
  have hv0F : v0 ∈ F0 := FiniteVectors.self_mem_orbitSpan ρ v0
  set d := Module.finrank ℂ F0
  set bF := Module.finBasis ℂ F0
  choose ℓ hℓ using fun i => LinearMap.exists_extend (bF.coord i)
  have hℓF : ∀ i (y : F0), ℓ i (y : V) = bF.repr y i := fun i y => by
    have := LinearMap.congr_fun (hℓ i) y
    simpa using this
  have hexp : ∀ y ∈ F0, y = ∑ i, ℓ i y • (bF i : V) := by
    intro y hy
    have := congrArg Subtype.val (bF.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    conv_lhs => rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hℓF i ⟨y, hy⟩]
  have hbF : ∀ i j, ℓ i (bF j : V) = if i = j then 1 else 0 := fun i j => by
    rw [hℓF i (bF j), Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  let τf : Matrix.unitaryGroup (Fin n) ℝ → Matrix (Fin d) (Fin d) ℂ :=
    fun k => Matrix.of fun i j => ℓ i (ρ k (bF j))
  have hτ1 : τf 1 = 1 := by
    ext i j
    simp only [τf, Matrix.of_apply, map_one, Module.End.one_apply, hbF, Matrix.one_apply]
  have hτmul : ∀ k k', τf (k * k') = τf k * τf k' := by
    intro k k'
    ext i j
    simp only [τf, Matrix.of_apply, Matrix.mul_apply, map_mul, Module.End.mul_apply]
    have h := hexp (ρ k' (bF j)) (hF0 k' _ (bF j).2)
    conv_lhs => rw [h]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  let τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ := ⟨⟨τf, hτ1⟩, hτmul⟩
  have hτapply : ∀ k i j, τ k i j = ℓ i (ρ k (bF j)) := fun _ _ _ => rfl
  let D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun X => Matrix.of fun i j =>
        ℓ i (π ((1 : ℂ) ⊗ₜ RealJacquetFrobenius.skewPart X) (bF j))
      map_add' := fun X Y => by
        ext i j
        simp [map_add, TensorProduct.tmul_add]
      map_smul' := fun r X => by
        ext i j
        simp only [map_smul, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
        have hsm : ∀ t : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, r • t = (r : ℂ) • t := fun t => by
          rw [← algebraMap_smul ℂ r t]; rfl
        rw [TensorProduct.tmul_smul, hsm, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
          Complex.real_smul] }
  have hDapply : ∀ X i j, D X i j = ℓ i (π ((1 : ℂ) ⊗ₜ RealJacquetFrobenius.skewPart X) (bF j)) :=
    fun _ _ _ => rfl
  let T0 : (Fin d → ℂ) →ₗ[ℂ] V := F0.subtype ∘ₗ bF.equivFun.symm.toLinearMap
  have hT0 : ∀ x, T0 x = ∑ i, x i • (bF i : V) := by
    intro x
    change ((bF.equivFun.symm x : F0) : V) = _
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hd : 0 < d := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨v0, hv0F⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  refine ⟨d, τ, D, T0, ?_, ?_, ?_, ?_, hd⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hgk.2.1 (bF j) (ℓ i)
  · intro γ X h0 hX i j
    have hskew := transpose_eq_neg_of_curve h0 hX
    have := hgk.2.2.1 γ X h0 hX (bF j) (ℓ i)
    rw [hDapply, skewPart_eq_self hskew]
    exact this
  · intro k x
    rw [hT0, hT0, map_sum]
    simp only [map_smul]
    have : ∀ j, ρ k (bF j : V) = ∑ i, τ k i j • (bF i : V) := fun j => by
      rw [hexp (ρ k (bF j)) (hF0 k _ (bF j).2)]
      rfl
    simp only [this, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  · intro h
    have := LinearMap.congr_fun h (Pi.single ⟨0, hd⟩ 1)
    rw [hT0, LinearMap.zero_apply] at this
    have hb : (bF ⟨0, hd⟩ : V) = 0 := by
      rw [Finset.sum_eq_single ⟨0, hd⟩ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (by simp)] at this
      simpa using this
    exact bF.ne_zero ⟨0, hd⟩ (Subtype.ext hb)

end RealSubquotient

end Langlands.Archimedean
