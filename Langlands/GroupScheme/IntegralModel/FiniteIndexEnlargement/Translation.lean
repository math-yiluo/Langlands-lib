import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.IntegralPoints

/-! # Translations of coordinates by generic points

For a commutative Hopf algebra `A` over `R`, a field `K` over `R`, and a group `P` acting through
an evaluation homomorphism `ev : P →* WithConv (A →ₐ[R] K)` into the convolution monoid, we define
left and right translations of coordinates as algebra maps `A →ₐ[R] K ⊗[R] A`, and prove that a
translate is again a coordinate as soon as it is integral at all integral points. -/

noncomputable section

universe u

open TensorProduct WithConv

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Integral

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

/-- The `K`-linear extension of an integral point `σ` of `C` to `K ⊗[R] C`. -/
abbrev pointExt {C : Type u} [CommRing C] [Algebra R C] (σ : C →ₐ[R] R) :
    K ⊗[R] C →ₐ[R] K :=
  Algebra.TensorProduct.productMap (AlgHom.id R K) ((Algebra.ofId R K).comp σ)

/-- Every element of `K ⊗[R] C` has a nonzero integral multiple coming from `C`. -/
theorem exists_smul_eq_tmul [IsDomain R] [IsFractionRing R K] {C : Type u} [CommRing C]
    [Algebra R C] (t : K ⊗[R] C) : ∃ s : R, s ≠ 0 ∧ ∃ g : C, s • t = (1 : K) ⊗ₜ[R] g := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨s, nonZeroDivisors.ne_zero s.2, r • a, ?_⟩
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm, hrs,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, g₁, h₁⟩ := h₁
    obtain ⟨s₂, hs₂, g₂, h₂⟩ := h₂
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, s₂ • g₁ + s₁ • g₂, ?_⟩
    have e₁ : (s₁ * s₂) • t₁ = (1 : K) ⊗ₜ[R] (s₂ • g₁) := by
      rw [mul_comm, mul_smul, h₁, TensorProduct.tmul_smul]
    have e₂ : (s₁ * s₂) • t₂ = (1 : K) ⊗ₜ[R] (s₁ • g₂) := by
      rw [mul_smul, h₂, TensorProduct.tmul_smul]
    rw [smul_add, e₁, e₂, TensorProduct.tmul_add]

/-- A nonzero element of a discrete valuation ring divides a power of a uniformiser. -/
theorem exists_pow_eq_mul [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {s : R} (hs : s ≠ 0) : ∃ (N : ℕ) (t : R), ϖ ^ N = s * t := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨n, (↑u⁻¹ : R), ?_⟩
  rw [mul_comm (u : R), mul_assoc, Units.mul_inv, mul_one]

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K]

/-- **Integral criterion.** An element of `K ⊗[R] C`, for `C` smooth over `R`, all of whose
values at integral points are integral, comes from `C`. -/
theorem exists_tmul_eq_of_forall {C : Type u} [CommRing C] [Algebra R C] [Algebra.Smooth R C]
    (t : K ⊗[R] C) (ht : ∀ σ : C →ₐ[R] R, pointExt σ t ∈ (algebraMap R K).range) :
    ∃ c : C, (1 : K) ⊗ₜ[R] c = t := by
  obtain ⟨s, hs, g, hg⟩ := exists_smul_eq_tmul (K := K) t
  have hdvd : ∀ σ : C →ₐ[R] R, s ∣ σ g := by
    intro σ
    obtain ⟨r, hr⟩ := ht σ
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    have h1 : pointExt (K := K) σ (s • t) = algebraMap R K (σ g) := by
      rw [hg, Algebra.TensorProduct.productMap_apply_tmul]
      simp
    rw [map_smul, ← hr, Algebra.smul_def] at h1
    rw [map_mul, ← h1]
  obtain ⟨c, hc⟩ := dvd_of_forall_dvd hs hdvd
  have hs' : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  have key : algebraMap R K s • ((1 : K) ⊗ₜ[R] c) = algebraMap R K s • t := by
    rw [algebraMap_smul, algebraMap_smul, hg, hc, ← Algebra.smul_def, TensorProduct.tmul_smul]
  refine ⟨c, ?_⟩
  calc (1 : K) ⊗ₜ[R] c
      = (algebraMap R K s)⁻¹ • (algebraMap R K s • ((1 : K) ⊗ₜ[R] c)) := by
        rw [smul_smul, inv_mul_cancel₀ hs', one_smul]
    _ = t := by rw [key, smul_smul, inv_mul_cancel₀ hs', one_smul]

end Integral

section Group

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {A : Type u} [CommRing A] [HopfAlgebra R A] {P : Type*} [Group P]
  (ev : P →* WithConv (A →ₐ[R] K))

/-- The `K`-linear extension of the evaluation at `y` to `K ⊗[R] A`. -/
def evalExt (y : P) : K ⊗[R] A →ₐ[R] K :=
  Algebra.TensorProduct.productMap (AlgHom.id R K) (ev y).ofConv

/-- Left translation by `x`: the coordinate `y ↦ a (x * y)`, with coefficients in `K`. -/
def leftTrans (x : P) : A →ₐ[R] K ⊗[R] A :=
  (Algebra.TensorProduct.map (ev x).ofConv (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A)

/-- Right translation by `x`: the coordinate `y ↦ a (y * x)`, with coefficients in `K`. -/
def rightTrans (x : P) : A →ₐ[R] K ⊗[R] A :=
  (Algebra.TensorProduct.comm R A K).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R A) (ev x).ofConv).comp (Bialgebra.comulAlgHom R A))

theorem evalExt_tmul (y : P) (c : K) (a : A) : evalExt ev y (c ⊗ₜ[R] a) = c * ev y a :=
  rfl

theorem evalExt_one_tmul (y : P) (a : A) : evalExt ev y ((1 : K) ⊗ₜ[R] a) = ev y a := by
  rw [evalExt_tmul, one_mul]

theorem ev_mul_ofConv (x y : P) :
    (ev (x * y)).ofConv =
      (Algebra.TensorProduct.productMap (ev x).ofConv (ev y).ofConv).comp
        (Bialgebra.comulAlgHom R A) := by
  rw [map_mul, AlgHom.convMul_def, WithConv.ofConv_toConv,
    Algebra.TensorProduct.productMap_eq_comp_map, AlgHom.comp_assoc]

theorem ev_one_apply (a : A) : ev 1 a = algebraMap R K (Coalgebra.counit a) := by
  rw [map_one]
  rfl

theorem ev_algebraMap (y : P) (r : R) : ev y (algebraMap R A r) = algebraMap R K r :=
  (ev y).ofConv.commutes r

theorem evalExt_comp_leftTrans (x y : P) :
    (evalExt ev y).comp (leftTrans ev x) = (ev (x * y)).ofConv := by
  rw [ev_mul_ofConv, evalExt, leftTrans, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [Algebra.TensorProduct.productMap_apply_tmul]

theorem evalExt_comp_rightTrans (x y : P) :
    (evalExt ev y).comp (rightTrans ev x) = (ev (y * x)).ofConv := by
  rw [ev_mul_ofConv, evalExt, rightTrans, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [Algebra.TensorProduct.productMap_apply_tmul, mul_comm]

theorem evalExt_leftTrans (x y : P) (a : A) :
    evalExt ev y (leftTrans ev x a) = ev (x * y) a :=
  DFunLike.congr_fun (evalExt_comp_leftTrans ev x y) a

theorem evalExt_rightTrans (x y : P) (a : A) :
    evalExt ev y (rightTrans ev x a) = ev (y * x) a :=
  DFunLike.congr_fun (evalExt_comp_rightTrans ev x y) a

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K] [Algebra.Smooth R A]
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ)

include hU hsurj in
/-- A `K`-linear combination of coordinates whose values at the integral points `U` are integral
comes from `A`. -/
theorem exists_tmul_eq_of_forall_mem (t : K ⊗[R] A)
    (ht : ∀ u ∈ U, evalExt ev u t ∈ (algebraMap R K).range) :
    ∃ b : A, (1 : K) ⊗ₜ[R] b = t := by
  apply exists_tmul_eq_of_forall
  intro σ
  obtain ⟨u, hu⟩ := hsurj σ
  have huU : u ∈ U := (hU u).2 fun a => ⟨σ a, by rw [hu]; rfl⟩
  have hpe : pointExt (K := K) σ = evalExt ev u := by
    rw [evalExt, hu]
  rw [hpe]
  exact ht u huU

include hU hsurj in
/-- **Translation lemma.** If the left translate of `a` by `x` is integral at all integral
points, it is a coordinate. -/
theorem exists_leftTrans_eq (x : P) (a : A)
    (h : ∀ u ∈ U, ev (x * u) a ∈ (algebraMap R K).range) :
    ∃ b : A, (1 : K) ⊗ₜ[R] b = leftTrans ev x a :=
  exists_tmul_eq_of_forall_mem ev U hU hsurj _ fun u hu => by
    rw [evalExt_leftTrans]
    exact h u hu

include hU hsurj in
/-- **Translation lemma**, right-handed version. -/
theorem exists_rightTrans_eq (x : P) (a : A)
    (h : ∀ u ∈ U, ev (u * x) a ∈ (algebraMap R K).range) :
    ∃ b : A, (1 : K) ⊗ₜ[R] b = rightTrans ev x a :=
  exists_tmul_eq_of_forall_mem ev U hU hsurj _ fun u hu => by
    rw [evalExt_rightTrans]
    exact h u hu

include hU hsurj in
/-- Values-level translation lemma: a coordinate realising the left translate. -/
theorem exists_left_translate (x : P) (a : A)
    (h : ∀ u ∈ U, ev (x * u) a ∈ (algebraMap R K).range) :
    ∃ b : A, ∀ y, ev y b = ev (x * y) a := by
  obtain ⟨b, hb⟩ := exists_leftTrans_eq ev U hU hsurj x a h
  refine ⟨b, fun y => ?_⟩
  rw [← evalExt_one_tmul, hb, evalExt_leftTrans]

omit [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra.Smooth R A] in
include hU in
/-- Left translates of a coordinate have bounded denominators on a coset `x U`. -/
theorem exists_pow_smul_mem {ϖ : R} (hϖ : Irreducible ϖ) (x : P) (a : A) :
    ∃ N : ℕ, ∀ u ∈ U, ϖ ^ N • ev (x * u) a ∈ (algebraMap R K).range := by
  obtain ⟨s, hs, g, hg⟩ := exists_smul_eq_tmul (K := K) (leftTrans ev x a)
  obtain ⟨N, t, hNt⟩ := exists_pow_eq_mul hϖ hs
  refine ⟨N, fun u hu => ?_⟩
  have h1 : s • ev (x * u) a = ev u g := by
    rw [← evalExt_leftTrans, ← map_smul, hg, evalExt_one_tmul]
  rw [hNt, mul_comm, mul_smul, h1]
  obtain ⟨r, hr⟩ := (hU u).1 hu g
  exact ⟨t * r, by rw [map_mul, hr, Algebra.smul_def]⟩

end Group

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
