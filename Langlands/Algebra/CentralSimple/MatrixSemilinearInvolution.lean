import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Equiv

/-! # Semilinear involutions descend from matrix algebras to division rings -/

namespace Langlands.Algebra.CentralSimple

open Matrix

section Twist

variable {L D : Type*} [Field L] [DivisionRing D] [Algebra L D]

/-- A `σ`-semilinear additive anti-endomorphism `θ₀` of a division ring whose square is the
inner automorphism of an element `a` fixed up to inversion by `θ₀` can be twisted by an inner
automorphism into a `σ`-semilinear involution. -/
theorem exists_involution_of_sq_eq_conj (σ : L →+* L) (hσ : ∃ ω, σ ω ≠ ω)
    (θ₀ : D → D) (θ₀_add : ∀ x y, θ₀ (x + y) = θ₀ x + θ₀ y)
    (θ₀_mul : ∀ x y, θ₀ (x * y) = θ₀ y * θ₀ x)
    (θ₀_alg : ∀ c, θ₀ (algebraMap L D c) = algebraMap L D (σ c))
    (a : D) (ha : a ≠ 0) (hsq : ∀ x, θ₀ (θ₀ x) = a * x * a⁻¹) (hfix : θ₀ a = a⁻¹) :
    ∃ θ : D → D, (∀ x y, θ (x + y) = θ x + θ y) ∧ (∀ x y, θ (x * y) = θ y * θ x) ∧
      (∀ x, θ (θ x) = x) ∧ ∀ c, θ (algebraMap L D c) = algebraMap L D (σ c) := by
  have h1 : θ₀ 1 = 1 := by simpa using θ₀_alg 1
  have hinv : ∀ x, x ≠ 0 → θ₀ x⁻¹ = (θ₀ x)⁻¹ := by
    intro x hx
    have : θ₀ x⁻¹ * θ₀ x = 1 := by rw [← θ₀_mul, mul_inv_cancel₀ hx, h1]
    exact eq_inv_of_mul_eq_one_left this
  have hσσ : ∀ c, σ (σ c) = c := by
    intro c
    apply (algebraMap L D).injective
    rw [← θ₀_alg, ← θ₀_alg, hsq, ← Algebra.commutes, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  have hainv : θ₀ a⁻¹ = a := by rw [hinv a ha, hfix, inv_inv]
  let φ : D → D := fun x => a⁻¹ * θ₀ x
  have φ_add : ∀ x y, φ (x + y) = φ x + φ y := fun x y => by
    simp only [φ, θ₀_add, mul_add]
  have φφ : ∀ x, φ (φ x) = x := by
    intro x
    simp only [φ, θ₀_mul, hsq, hainv, mul_assoc, inv_mul_cancel₀ ha, mul_one,
      inv_mul_cancel_left₀ ha]
  have φ_smul : ∀ c x, φ (algebraMap L D c * x) = algebraMap L D (σ c) * φ x := by
    intro c x
    simp only [φ, θ₀_mul, θ₀_alg, ← Algebra.commutes, Algebra.left_comm]
  obtain ⟨ω, hω⟩ := hσ
  have key : ∃ b, b ≠ 0 ∧ φ b = b := by
    by_cases hb : 1 + φ 1 = 0
    · have hφ1 : φ 1 = -1 := eq_neg_of_add_eq_zero_right hb
      refine ⟨algebraMap L D ω + algebraMap L D (σ ω) * φ 1, ?_, ?_⟩
      · rw [hφ1, mul_neg_one, ← sub_eq_add_neg, ← map_sub]
        intro h
        apply hω
        have := (algebraMap L D).injective (h.trans (map_zero _).symm)
        exact (sub_eq_zero.1 this).symm
      · have hω' : φ (algebraMap L D ω) = algebraMap L D (σ ω) * φ 1 := by
          simpa using φ_smul ω 1
        rw [φ_add, hω', φ_smul, φφ, hσσ, mul_one, add_comm]
    · exact ⟨1 + φ 1, hb, by rw [φ_add, φφ, add_comm]⟩
  obtain ⟨b, hb0, hbφ⟩ := key
  have hθb : θ₀ b = a * b := by
    have : a⁻¹ * θ₀ b = b := hbφ
    calc θ₀ b = a * (a⁻¹ * θ₀ b) := (mul_inv_cancel_left₀ ha _).symm
      _ = a * b := by rw [this]
  have hθbinv : θ₀ b⁻¹ = b⁻¹ * a⁻¹ := by rw [hinv b hb0, hθb, mul_inv_rev]
  refine ⟨fun x => b * θ₀ x * b⁻¹, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [θ₀_add, mul_add, add_mul]
  · intro x y
    simp only [θ₀_mul, mul_assoc, inv_mul_cancel_left₀ hb0]
  · intro x
    simp only [θ₀_mul, hθbinv, hsq, hθb, mul_assoc, inv_mul_cancel_left₀ ha,
      mul_inv_cancel_left₀ hb0, mul_inv_cancel₀ hb0, mul_one]
  · intro c
    simp only [θ₀_alg, ← Algebra.commutes, mul_assoc, mul_inv_cancel₀ hb0, mul_one]

end Twist

section MatrixUnits

variable {D ι : Type*} [DivisionRing D] [Fintype ι]

/-- Right multiplication of row vectors by a square matrix, as a linear endomorphism of the
left `D`-module of row vectors. -/
def rowMulLinear (X : Matrix ι ι D) : (ι → D) →ₗ[D] (ι → D) where
  toFun v := v ᵥ* X
  map_add' v w := add_vecMul X v w
  map_smul' d v := smul_vecMul d v X

@[simp] theorem rowMulLinear_apply (X : Matrix ι ι D) (v : ι → D) :
    rowMulLinear X v = v ᵥ* X := rfl

variable [DecidableEq ι]

/-- The image of a matrix unit `E i₀ i₀` under an additive, unital anti-endomorphism of a
matrix algebra over a division ring is Murray–von Neumann equivalent to `E i₀ i₀`. -/
theorem exists_mul_eq_single_of_antiHom (τ : Matrix ι ι D → Matrix ι ι D)
    (τ_add : ∀ X Y, τ (X + Y) = τ X + τ Y) (τ_mul : ∀ X Y, τ (X * Y) = τ Y * τ X)
    (τ_one : τ 1 = 1) (i₀ : ι) :
    ∃ y z : Matrix ι ι D, z * y = single i₀ i₀ 1 ∧ y * z = τ (single i₀ i₀ 1) := by
  classical
  have τ0 : τ 0 = 0 := by
    have := τ_add 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let F : ι → ι → Matrix ι ι D := fun i j => τ (single j i 1)
  have FF : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp only [F]
    rw [← τ_mul]
    split_ifs with h
    · subst h
      rw [single_mul_single_same, one_mul]
    · rw [show single l k (1 : D) * single j i 1 = 0 by simp [Ne.symm h], τ0]
  have Fsum : ∑ i, F i i = 1 := by
    have : ∑ i, F i i = τ (∑ i, single i i (1 : D)) := by
      exact (map_sum (AddMonoidHom.mk' τ τ_add) (fun i => single i i (1 : D)) Finset.univ).symm
    rw [this, sum_single_one, τ_one]
  set F₀ := F i₀ i₀ with hF₀def
  have F₀idem : F₀ * F₀ = F₀ := by simpa using FF i₀ i₀ i₀ i₀
  set W := LinearMap.range (rowMulLinear F₀) with hW
  have memW : ∀ v, v ∈ W ↔ v ᵥ* F₀ = v := by
    intro v
    constructor
    · rintro ⟨u, rfl⟩
      simp [vecMul_vecMul, F₀idem]
    · intro h
      exact ⟨v, h⟩
  let Ψ : (ι → D) →ₗ[D] (ι → W) := LinearMap.pi fun i =>
    (rowMulLinear (F i i₀)).codRestrict W (fun v => by
      rw [memW]
      simp [hF₀def, FF, vecMul_vecMul])
  let Ψ' : (ι → W) →ₗ[D] (ι → D) :=
    ∑ i, (rowMulLinear (F i₀ i)) ∘ₗ W.subtype ∘ₗ LinearMap.proj i
  have h1 : Ψ ∘ₗ Ψ' = LinearMap.id := by
    refine LinearMap.ext fun w => funext fun i => Subtype.ext ?_
    have hw : ∀ j, (w j : ι → D) ᵥ* (if j = i then F i₀ i₀ else 0) =
        if j = i then (w j : ι → D) else 0 := by
      intro j
      split_ifs with h
      · exact (memW _).1 (w j).2
      · exact vecMul_zero _
    simp only [Ψ, Ψ', LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.codRestrict_apply,
      LinearMap.sum_apply, LinearMap.proj_apply, Submodule.subtype_apply,
      rowMulLinear_apply, LinearMap.id_apply, sum_vecMul, vecMul_vecMul, FF, hw,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : Ψ' ∘ₗ Ψ = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [Ψ, Ψ', LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.codRestrict_apply,
      LinearMap.sum_apply, LinearMap.proj_apply, Submodule.subtype_apply,
      rowMulLinear_apply, LinearMap.id_apply, vecMul_vecMul, FF, ite_true]
    rw [← vecMul_sum, Fsum, vecMul_one]
  have hrank : Module.finrank D W = 1 := by
    have := (LinearEquiv.ofLinearMap Ψ Ψ' h1 h2).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at this
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    exact (Nat.eq_of_mul_eq_mul_left hpos (this.symm.trans (mul_one _).symm))
  obtain ⟨u₀, hu₀, hspan⟩ := finrank_eq_one_iff'.1 hrank
  set u : ι → D := (u₀ : ι → D) with hu
  have hu0 : u ≠ 0 := fun h => hu₀ (Subtype.ext h)
  have huF : u ᵥ* F₀ = u := (memW u).1 u₀.2
  have hrow : ∀ j, ∃ c : D, c • u = Pi.single j 1 ᵥ* F₀ := by
    intro j
    obtain ⟨c, hc⟩ := hspan ⟨Pi.single j 1 ᵥ* F₀, Pi.single j 1, rfl⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hrow
  have hF₀ : ∀ j k, F₀ j k = c j * u k := by
    intro j k
    have := congrFun (hc j) k
    simp only [Pi.smul_apply, smul_eq_mul, single_vecMul, one_mul, row_apply] at this
    exact this.symm
  have hs : ∑ j, u j * c j = 1 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hu0
    have := congrFun huF k
    simp only [vecMul, dotProduct, hF₀, ← mul_assoc, ← Finset.sum_mul] at this
    exact mul_right_cancel₀ hk (this.trans (one_mul _).symm)
  refine ⟨of fun j k => if k = i₀ then c j else 0, of fun i k => if i = i₀ then u k else 0,
    ?_, ?_⟩
  · ext i k
    simp only [mul_apply, of_apply, single]
    by_cases hi : i = i₀ <;> by_cases hk : k = i₀ <;> simp [hi, hk, hs, @eq_comm _ i₀]
  · ext j k
    change _ = F₀ j k
    rw [hF₀ j k]
    simp [mul_apply, of_apply]

end MatrixUnits

section Corner

variable {L D ι : Type*} [Field L] [DivisionRing D] [Algebra L D] [Fintype ι] [DecidableEq ι]

/-- A `σ`-semilinear involution of a matrix algebra over a division ring induces one on the
division ring, for any nontrivial `σ`. -/
theorem exists_semilinear_involution_of_matrix [Nonempty ι] (σ : L →+* L) (hσ : ∃ ω, σ ω ≠ ω)
    (τ : Matrix ι ι D → Matrix ι ι D) (τ_add : ∀ X Y, τ (X + Y) = τ X + τ Y)
    (τ_mul : ∀ X Y, τ (X * Y) = τ Y * τ X) (τ_invol : ∀ X, τ (τ X) = X)
    (τ_alg : ∀ c, τ (algebraMap L (Matrix ι ι D) c) = algebraMap L (Matrix ι ι D) (σ c)) :
    ∃ θ : D → D, (∀ x y, θ (x + y) = θ x + θ y) ∧ (∀ x y, θ (x * y) = θ y * θ x) ∧
      (∀ x, θ (θ x) = x) ∧ ∀ c, θ (algebraMap L D c) = algebraMap L D (σ c) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have τ_one : τ 1 = 1 := by simpa using τ_alg 1
  obtain ⟨y', z', hzy', hyz'⟩ := exists_mul_eq_single_of_antiHom τ τ_add τ_mul τ_one i₀
  set e : Matrix ι ι D := single i₀ i₀ 1 with he
  set f := τ e with hf
  have ee : e * e = e := by simp [he]
  have ff : f * f = f := by rw [hf, ← τ_mul, ee]
  have τf : τ f = e := τ_invol e
  obtain ⟨z, y, hez, hzf, hfy, hye, hzy, hyz⟩ : ∃ z y : Matrix ι ι D, e * z = z ∧ z * f = z ∧
      f * y = y ∧ y * e = y ∧ z * y = e ∧ y * z = f := by
    refine ⟨z' * f, y' * e, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hzy']
      calc z' * y' * (z' * f) = z' * (y' * z') * f := by simp only [mul_assoc]
        _ = z' * f * f := by rw [hyz']
        _ = z' * f := by rw [mul_assoc, ff]
    · rw [mul_assoc, ff]
    · rw [← hyz']
      calc y' * z' * (y' * e) = y' * (z' * y') * e := by simp only [mul_assoc]
        _ = y' * e * e := by rw [hzy']
        _ = y' * e := by rw [mul_assoc, ee]
    · rw [mul_assoc, ee]
    · rw [← hyz']
      calc z' * (y' * z') * (y' * e) = z' * y' * (z' * y') * e := by simp only [mul_assoc]
        _ = e := by rw [hzy', ee, ee]
    · rw [← hzy']
      calc y' * (z' * y') * (z' * f) = y' * z' * (y' * z') * f := by simp only [mul_assoc]
        _ = f := by rw [hyz', ff, ff]
  let ιD : D → Matrix ι ι D := fun d => single i₀ i₀ d
  have ιD_mul : ∀ d₁ d₂, ιD d₁ * ιD d₂ = ιD (d₁ * d₂) := fun d₁ d₂ =>
    single_mul_single_same _ _ _ _ _
  have ιD_apply : ∀ d, ιD d i₀ i₀ = d := fun d => single_apply_same _ _ _
  have corner : ∀ X, e * X * e = ιD (X i₀ i₀) := by
    intro X
    simp [he, ιD]
  have ιD_e : ∀ d, ιD d * e = ιD d := by
    intro d
    simp [he, ιD]
  have e_ιD : ∀ d, e * ιD d = ιD d := by
    intro d
    simp [he, ιD]
  have ιD_alg : ∀ c, ιD (algebraMap L D c) = algebraMap L (Matrix ι ι D) c * e := by
    intro c
    show single i₀ i₀ (algebraMap L D c) = _
    rw [Algebra.algebraMap_eq_smul_one (A := Matrix ι ι D), smul_mul_assoc, one_mul, he,
      smul_single, Algebra.algebraMap_eq_smul_one]
  have sandwich : ∀ X, z * X * y = ιD ((z * X * y) i₀ i₀) := by
    intro X
    have h : e * (z * X * y) * e = z * X * y := by
      simp only [← mul_assoc, hez]
      simp only [mul_assoc, hye]
    rw [← corner, h]
  have τι_f : ∀ d, f * τ (ιD d) = τ (ιD d) := by
    intro d
    rw [hf, ← τ_mul, ιD_e]
  let θ₀ : D → D := fun d => (z * τ (ιD d) * y) i₀ i₀
  have θ₀_add : ∀ x x', θ₀ (x + x') = θ₀ x + θ₀ x' := by
    intro x x'
    simp only [θ₀, ιD, single_add, τ_add, mul_add, add_mul, add_apply]
  have θ₀_mul : ∀ d₁ d₂, θ₀ (d₁ * d₂) = θ₀ d₂ * θ₀ d₁ := by
    intro d₁ d₂
    have h : z * τ (ιD (d₁ * d₂)) * y = (z * τ (ιD d₂) * y) * (z * τ (ιD d₁) * y) := by
      calc z * τ (ιD (d₁ * d₂)) * y = z * τ (ιD d₂) * (f * τ (ιD d₁)) * y := by
            rw [← ιD_mul, τ_mul, τι_f]
            simp only [mul_assoc]
        _ = (z * τ (ιD d₂) * y) * (z * τ (ιD d₁) * y) := by
            rw [← hyz]
            simp only [mul_assoc]
    show (z * τ (ιD (d₁ * d₂)) * y) i₀ i₀ = _
    rw [h, sandwich (τ (ιD d₂)), sandwich (τ (ιD d₁)), ιD_mul, ιD_apply]
  have θ₀_alg : ∀ c, θ₀ (algebraMap L D c) = algebraMap L D (σ c) := by
    intro c
    show (z * τ (ιD (algebraMap L D c)) * y) i₀ i₀ = _
    rw [ιD_alg, τ_mul, τ_alg, ← hf, ← Algebra.commutes, Algebra.left_comm, hzf, mul_assoc, hzy,
      ← ιD_alg, ιD_apply]
  let a : D := (z * τ y) i₀ i₀
  let a' : D := (τ z * y) i₀ i₀
  have hzτy : z * τ y = ιD a := by
    have hτye : τ y * e = τ y := by rw [← τf, ← τ_mul, hfy]
    have h : e * (z * τ y) * e = z * τ y := by rw [← mul_assoc, hez, mul_assoc, hτye]
    exact h.symm.trans (corner _)
  have hτzy : τ z * y = ιD a' := by
    have heτz : e * τ z = τ z := by rw [← τf, ← τ_mul, hzf]
    have h : e * (τ z * y) * e = τ z * y := by rw [← mul_assoc, heτz, mul_assoc, hye]
    exact h.symm.trans (corner _)
  have haa' : a * a' = 1 := by
    have h : ιD (a * a') = ιD 1 := by
      rw [← ιD_mul, ← hzτy, ← hτzy]
      calc z * τ y * (τ z * y) = z * (τ y * τ z) * y := by simp only [mul_assoc]
        _ = e := by rw [← τ_mul, hzy, ← hf, hzf, hzy]
    rw [← ιD_apply (a * a'), h, ιD_apply]
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one haa'
  have ha' : a' = a⁻¹ := eq_inv_of_mul_eq_one_right haa'
  have hsq : ∀ d, θ₀ (θ₀ d) = a * d * a⁻¹ := by
    intro d
    show (z * τ (ιD (θ₀ d)) * y) i₀ i₀ = _
    have h : ιD (θ₀ d) = z * τ (ιD d) * y := (sandwich _).symm
    rw [h, τ_mul, τ_mul, τ_invol, ← ha',
      show z * (τ y * (ιD d * τ z)) * y = (z * τ y) * ιD d * (τ z * y) by simp only [mul_assoc],
      hzτy, hτzy, ιD_mul, ιD_mul, ιD_apply]
  have hfix : θ₀ a = a⁻¹ := by
    show (z * τ (ιD a) * y) i₀ i₀ = _
    rw [← hzτy, τ_mul, τ_invol, ← ha',
      show z * (y * τ z) * y = (z * y) * (τ z * y) by simp only [mul_assoc], hzy, hτzy, e_ιD,
      ιD_apply]
  exact exists_involution_of_sq_eq_conj σ hσ θ₀ θ₀_add θ₀_mul θ₀_alg a ha hsq hfix

end Corner

/-- **Involutions of the second kind descend along Wedderburn decompositions.**
If an `L`-algebra `B` is isomorphic to a matrix algebra `Matrix ι ι D` over a division
`L`-algebra `D` and carries an additive, anti-multiplicative, involutive map restricting to a
nontrivial ring endomorphism `σ` of `L`, then `D` carries such a map for the same `σ`. -/
theorem exists_semilinear_involution_of_algEquiv_matrix
    {L D B ι : Type*} [Field L] [DivisionRing D] [Algebra L D] [Ring B] [Algebra L B]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Φ : B ≃ₐ[L] Matrix ι ι D) (σ : L →+* L) (hσ : ∃ ω, σ ω ≠ ω)
    (τ : B → B) (τ_add : ∀ x y, τ (x + y) = τ x + τ y) (τ_mul : ∀ x y, τ (x * y) = τ y * τ x)
    (τ_invol : ∀ x, τ (τ x) = x) (τ_alg : ∀ c, τ (algebraMap L B c) = algebraMap L B (σ c)) :
    ∃ θ : D → D, (∀ x y, θ (x + y) = θ x + θ y) ∧ (∀ x y, θ (x * y) = θ y * θ x) ∧
      (∀ x, θ (θ x) = x) ∧ ∀ c, θ (algebraMap L D c) = algebraMap L D (σ c) := by
  refine exists_semilinear_involution_of_matrix σ hσ (fun X => Φ (τ (Φ.symm X))) ?_ ?_ ?_ ?_
  · intro X Y
    simp only [map_add, τ_add]
  · intro X Y
    simp only [map_mul, τ_mul]
  · intro X
    simp only [AlgEquiv.symm_apply_apply, τ_invol, AlgEquiv.apply_symm_apply]
  · intro c
    simp only [AlgEquiv.commutes, τ_alg]

end Langlands.Algebra.CentralSimple
