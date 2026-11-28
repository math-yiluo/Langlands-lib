import Langlands.Algebra.CentralSimple.RelativeNormMatrixChart
import Langlands.Algebra.ReducedCharpolyRegularPowers
import Langlands.Algebra.LocalReducedNormRegular
import Langlands.Algebra.ReducedNormScalarExtension

/-! # Regular unitary elements at a place split in the quadratic extension -/

noncomputable section

universe u

open scoped TensorProduct
open Polynomial

namespace Langlands.CentralSimple.UnitaryPoints

open Langlands.GroupScheme Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]

section Coefficients

variable (F E B) (K : Type u) [CommRing K] [Algebra F K]

/-- The map `ψ = id ⊗ (E → B) : K ⊗[F] E → K ⊗[F] B`. -/
abbrev centerMap : K ⊗[F] E →ₐ[K] K ⊗[F] B :=
  Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B)

/-- The conjugation `id ⊗ conj` of `K ⊗[F] E`. -/
abbrev centerConj : K ⊗[F] E →ₐ[K] K ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id K K) (conjugation F E).toAlgHom

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- The image of `ψ` is central. -/
theorem centerMap_commute (ℓ : K ⊗[F] E) (y : K ⊗[F] B) :
    centerMap F E B K ℓ * y = y * centerMap F E B K ℓ := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    induction y using TensorProduct.inductionOn with
    | tmul k' b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
        Algebra.TensorProduct.tmul_mul_tmul, mul_comm k k', Algebra.commutes]
    | add y y' hy hy' => rw [mul_add, add_mul, hy, hy']
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, add_mul, mul_add, hℓ, hℓ']

theorem centerConj_centerConj (ℓ : K ⊗[F] E) :
    centerConj F E K (centerConj F E K ℓ) = ℓ := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg _ (conjugation_involutive F E e)
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ']

variable {F E B}

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))
include hτ

/-- `τ_K ∘ ψ = ψ ∘ c`. -/
theorem baseChange_centerMap (ℓ : K ⊗[F] E) :
    τ.baseChange K (centerMap F E B K ℓ) = centerMap F E B K (centerConj F E K ℓ) := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      FirstKindInvolution.baseChange_tmul, hτ]
    rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, FirstKindInvolution.map_add, hℓ, hℓ', map_add, map_add]

omit hτ [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
theorem baseChange_pow (x : K ⊗[F] B) (i : ℕ) :
    τ.baseChange K (x ^ i) = (τ.baseChange K x) ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, FirstKindInvolution.map_mul, ih, pow_succ']

/-- `τ_K (f(x)) = c(f)(τ_K x)` for polynomials evaluated through `ψ`. -/
theorem baseChange_eval₂ (f : (K ⊗[F] E)[X]) (x : K ⊗[F] B) :
    τ.baseChange K (f.eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) x) =
      (f.map (centerConj F E K : K ⊗[F] E →+* K ⊗[F] E)).eval₂
        (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) (τ.baseChange K x) := by
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range' _ (n := f.natDegree + 1)
    (natDegree_map_le.trans_lt (Nat.lt_succ_self _)), FirstKindInvolution.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FirstKindInvolution.map_mul, baseChange_pow, coeff_map]
  change τ.baseChange K x ^ i * τ.baseChange K (centerMap F E B K (f.coeff i)) =
    centerMap F E B K (centerConj F E K (f.coeff i)) * τ.baseChange K x ^ i
  rw [baseChange_centerMap K τ hτ, centerMap_commute]

end Coefficients

section Split

variable (F E) (K : Type u) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- The projection `k ⊗ e ↦ k e` of `K ⊗[F] E` for an `E`-algebra `K`. -/
abbrev splitProj₁ : K ⊗[F] E →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) (IsScalarTower.toAlgHom F E K)
    (fun _ _ => Commute.all _ _)

/-- The projection `k ⊗ e ↦ k ē` of `K ⊗[F] E` for an `E`-algebra `K`. -/
abbrev splitProj₂ : K ⊗[F] E →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K)
    ((IsScalarTower.toAlgHom F E K).comp (conjugation F E).toAlgHom)
    (fun _ _ => Commute.all _ _)

variable {F E}

theorem splitProj₁_centerConj (ℓ : K ⊗[F] E) :
    splitProj₁ F E K (centerConj F E K ℓ) = splitProj₂ F E K ℓ := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e => rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ', map_add]

theorem splitProj₂_centerConj (ℓ : K ⊗[F] E) :
    splitProj₂ F E K (centerConj F E K ℓ) = splitProj₁ F E K ℓ := by
  rw [← splitProj₁_centerConj, centerConj_centerConj]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
theorem tensorProj_comm_eq_splitProj₁ (ℓ : K ⊗[F] E) :
    HermitianMatrix.tensorProj F E (IsScalarTower.toAlgHom F E K)
      (Algebra.TensorProduct.comm F K E ℓ) = splitProj₁ F E K ℓ := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    rw [Algebra.TensorProduct.comm_tmul, HermitianMatrix.tensorProj_tmul,
      Algebra.TensorProduct.lift_tmul, mul_comm]
    rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ', map_add]

theorem tensorProj_comm_eq_splitProj₂ (ℓ : K ⊗[F] E) :
    HermitianMatrix.tensorProj F E
        ((IsScalarTower.toAlgHom F E K).comp (conjugation F E).toAlgHom)
      (Algebra.TensorProduct.comm F K E ℓ) = splitProj₂ F E K ℓ := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    rw [Algebra.TensorProduct.comm_tmul, HermitianMatrix.tensorProj_tmul,
      Algebra.TensorProduct.lift_tmul, mul_comm]
    rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ', map_add]

/-- The two projections of `K ⊗[F] E` are jointly injective. -/
theorem splitProj_injective {ℓ ℓ' : K ⊗[F] E} (h₁ : splitProj₁ F E K ℓ = splitProj₁ F E K ℓ')
    (h₂ : splitProj₂ F E K ℓ = splitProj₂ F E K ℓ') : ℓ = ℓ' := by
  apply (Algebra.TensorProduct.comm F K E).injective
  apply HermitianMatrix.tensorProj_injective₂ F E (IsScalarTower.toAlgHom F E K)
  · rw [tensorProj_comm_eq_splitProj₁, tensorProj_comm_eq_splitProj₁, h₁]
  · rw [tensorProj_comm_eq_splitProj₂, tensorProj_comm_eq_splitProj₂, h₂]

/-- The two projections of `K ⊗[F] E` are jointly surjective. -/
theorem splitProj_surjective (r s : K) :
    ∃ ℓ : K ⊗[F] E, splitProj₁ F E K ℓ = r ∧ splitProj₂ F E K ℓ = s := by
  obtain ⟨w, h₁, h₂⟩ := HermitianMatrix.tensorProj_surjective₂ F E
    (IsScalarTower.toAlgHom F E K) r s
  refine ⟨(Algebra.TensorProduct.comm F K E).symm w, ?_, ?_⟩
  · rw [← tensorProj_comm_eq_splitProj₁, AlgEquiv.apply_symm_apply, h₁]
  · rw [← tensorProj_comm_eq_splitProj₂, AlgEquiv.apply_symm_apply, h₂]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- On the image of `ψ`, the quotient map `K ⊗[F] B → K ⊗[E] B` is the first projection. -/
theorem tensorQuotient_centerMap (ℓ : K ⊗[F] E) :
    tensorQuotient F E B K (centerMap F E B K ℓ) =
      algebraMap K (K ⊗[E] B) (splitProj₁ F E K ℓ) := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul k e =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      tensorQuotient_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := B), TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
    rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ', map_add, map_add]

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))
include hτ

/-- The second component `y ↦ q(τ_K y)` on the image of `ψ` is the second projection. -/
theorem tensorQuotient_baseChange_centerMap (ℓ : K ⊗[F] E) :
    tensorQuotient F E B K (τ.baseChange K (centerMap F E B K ℓ)) =
      algebraMap K (K ⊗[E] B) (splitProj₂ F E K ℓ) := by
  rw [baseChange_centerMap K τ hτ, tensorQuotient_centerMap, splitProj₁_centerConj]

/-- The two components `q` and `q ∘ τ_K` of `K ⊗[F] B` are jointly surjective. -/
theorem split_surjective (a b : K ⊗[E] B) :
    ∃ y : K ⊗[F] B, tensorQuotient F E B K y = a ∧
      tensorQuotient F E B K (τ.baseChange K y) = b := by
  obtain ⟨ε, hε₁, hε₂⟩ := splitProj_surjective (F := F) (E := E) K 1 0
  obtain ⟨y₁, rfl⟩ := tensorQuotient_surjective F E B K a
  obtain ⟨y₂, rfl⟩ := tensorQuotient_surjective F E B K b
  refine ⟨centerMap F E B K ε * y₁ + τ.baseChange K y₂ * centerMap F E B K (1 - ε), ?_, ?_⟩
  · simp only [map_add, map_mul, tensorQuotient_centerMap, hε₁, map_sub, map_one, sub_self,
      one_mul, mul_zero, add_zero]
  · rw [FirstKindInvolution.map_add, FirstKindInvolution.map_mul, FirstKindInvolution.map_mul,
      FirstKindInvolution.apply_apply]
    simp only [map_add, map_mul, tensorQuotient_baseChange_centerMap K τ hτ, hε₂, map_sub,
      map_one, sub_zero, map_zero, mul_zero, zero_add, one_mul, FirstKindInvolution.map_one]

/-- The two components `q` and `q ∘ τ_K` of `K ⊗[F] B` are jointly injective. -/
theorem split_injective [FiniteDimensional E B] {y y' : K ⊗[F] B}
    (h₁ : tensorQuotient F E B K y = tensorQuotient F E B K y')
    (h₂ : tensorQuotient F E B K (τ.baseChange K y) =
      tensorQuotient F E B K (τ.baseChange K y')) : y = y' := by
  have : FiniteDimensional F E := .of_finrank_pos (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  let Φ : K ⊗[F] B →ₗ[K] (K ⊗[E] B) × (K ⊗[E] B) :=
    (tensorQuotient F E B K).toLinearMap.prod
      ((tensorQuotient F E B K).toLinearMap ∘ₗ (τ.baseChange K).toLinearMap)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨y, ha, hb⟩ := split_surjective K τ hτ a b
    exact ⟨y, Prod.ext ha hb⟩
  have hdim : Module.finrank K (K ⊗[F] B) = Module.finrank K ((K ⊗[E] B) × (K ⊗[E] B)) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_baseChange,
      ← Module.finrank_mul_finrank F E B, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      two_mul]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact hinj (Prod.ext h₁ h₂)

omit hτ [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- The first component of a polynomial evaluated through `ψ`. -/
theorem tensorQuotient_eval₂ (f : (K ⊗[F] E)[X]) (y : K ⊗[F] B) :
    tensorQuotient F E B K (f.eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) y) =
      aeval (tensorQuotient F E B K y) (f.map (splitProj₁ F E K : K ⊗[F] E →+* K)) := by
  have h : (tensorQuotient F E B K : K ⊗[F] B →+* K ⊗[E] B).comp
      (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) =
      (algebraMap K (K ⊗[E] B)).comp (splitProj₁ F E K : K ⊗[F] E →+* K) :=
    RingHom.ext (tensorQuotient_centerMap K)
  change (tensorQuotient F E B K : K ⊗[F] B →+* K ⊗[E] B) _ = _
  rw [hom_eval₂, h, aeval_def, eval₂_map]
  rfl

/-- The second component of a polynomial evaluated through `ψ`. -/
theorem tensorQuotient_baseChange_eval₂ (f : (K ⊗[F] E)[X]) (y : K ⊗[F] B) :
    tensorQuotient F E B K
        (τ.baseChange K (f.eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) y)) =
      aeval (tensorQuotient F E B K (τ.baseChange K y))
        (f.map (splitProj₂ F E K : K ⊗[F] E →+* K)) := by
  rw [baseChange_eval₂ K τ hτ, tensorQuotient_eval₂, Polynomial.map_map]
  congr 2
  exact RingHom.ext (splitProj₁_centerConj K)

/-- The second component of `ψ(ℓ) yⁱ`. -/
theorem tensorQuotient_baseChange_centerMap_mul_pow (ℓ : K ⊗[F] E) (y : K ⊗[F] B) (i : ℕ) :
    tensorQuotient F E B K (τ.baseChange K (centerMap F E B K ℓ * y ^ i)) =
      splitProj₂ F E K ℓ • tensorQuotient F E B K (τ.baseChange K y) ^ i := by
  rw [FirstKindInvolution.map_mul, map_mul, tensorQuotient_baseChange_centerMap K τ hτ,
    baseChange_pow, map_pow, Algebra.smul_def, Algebra.commutes]

end Split

section SplitRegular

variable [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))
include hτ

/-- **Regular unitary elements at a split place.** Let `K` be a complete nontrivially normed
field of characteristic zero which is an `E`-algebra (so `E ⊗[F] K ≅ K × K`). If `z ⊗ 1` is
the relative reduced norm of a unitary point of `K ⊗[F] B`, there are a unitary
`x ∈ K ⊗[F] B` and a monic conjugate-reciprocal `f` of degree `n` over `K ⊗[F] E` with
`f(x) = 0`, `f'(x)` a unit and `1, x, …, x^{n-1}` independent over `K ⊗[F] E`. -/
theorem exists_regular_unitary_of_split (K : Type u) [NontriviallyNormedField K]
    [CompleteSpace K] [CharZero K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
    (n : ℕ) (hn : Module.finrank E B = n ^ 2) (z : Eˣ)
    (x₀ : (K ⊗[F] B)ˣ) (hx₀ : x₀ ∈ unitaryPoints τ K)
    (hz : (relativeNorm F E B K x₀ : E ⊗[F] K) = (z : E) ⊗ₜ[F] (1 : K)) :
    ∃ (x : K ⊗[F] B) (f : (K ⊗[F] E)[X]),
      x * τ.baseChange K x = 1 ∧ f.Monic ∧ f.natDegree = n ∧
      (∀ i ≤ n, f.coeff (n - i) = (-1) ^ n * ((1 : K) ⊗ₜ[F] (z : E)) *
          Algebra.TensorProduct.map (AlgHom.id K K) (conjugation F E).toAlgHom (f.coeff i)) ∧
      f.eval₂ (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B) :
          K ⊗[F] E →+* K ⊗[F] B) x = 0 ∧
      IsUnit ((derivative f).eval₂ (Algebra.TensorProduct.map (AlgHom.id K K)
          (IsScalarTower.toAlgHom F E B) : K ⊗[F] E →+* K ⊗[F] B) x) ∧
      ∀ c : Fin n → K ⊗[F] E,
        ∑ i, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B) (c i) *
          x ^ (i : ℕ) = 0 → c = 0 := by
  classical
  have : IsSimpleRing (K ⊗[E] B) := isSimpleRing_baseChange E B K
  have : Algebra.IsCentral K (K ⊗[E] B) := isCentral_baseChange E B K
  obtain rfl : reducedDegree K (K ⊗[E] B) = n := by
    rw [reducedDegree_baseChange E B K, reducedDegree, hn, Nat.sqrt_eq']
  set n := reducedDegree K (K ⊗[E] B) with hn_def
  let q := tensorQuotient F E B K
  let φ := algebraMap E K
  -- the reduced norm of the first component
  have hN₀ : reducedNorm K (K ⊗[E] B) K (1 ⊗ₜ[K] q (x₀ : K ⊗[F] B)) = φ z := by
    have h1 := tensorProj_relativeNorm_eq_reducedNorm (F := F) (E := E) (B := B) K x₀
    rw [hz, HermitianMatrix.tensorProj_tmul, mul_one] at h1
    have h2 := reducedNorm_baseChange (⟨AlgCat.of E B⟩ : CSA.{u, u} E) K (q (x₀ : K ⊗[F] B))
    exact h2.trans h1.symm
  have hz0 : φ z ≠ 0 := (_root_.map_ne_zero _).mpr z.ne_zero
  have hN0 : reducedNorm K (K ⊗[E] B) K (1 ⊗ₜ[K] q (x₀ : K ⊗[F] B)) ≠ 0 := hN₀ ▸ hz0
  obtain ⟨a, ha, hsep⟩ := exists_norm_eq_with_separable_reducedCharpoly _ hN0
  set g := reducedCharpoly K (K ⊗[E] B) a with hg_def
  have hgm : g.Monic := reducedCharpoly_monic _ _ a
  have hgd : g.natDegree = n := reducedCharpoly_natDegree _ _ a
  have hg0 : g.coeff 0 = (-1) ^ n * φ z := by
    rw [hg_def, reducedCharpoly_coeff_zero, ha, hN₀]
  have hgz : g.coeff 0 ≠ 0 := by
    rw [hg0]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hz0
  have hga : aeval a g = 0 := aeval_reducedCharpoly a
  have hau : IsUnit a := isUnit_of_aeval_eq_zero hgz hga
  set u := hau.unit with hu_def
  have hua : (u : K ⊗[E] B) = a := hau.unit_spec
  -- `z z̄ = 1`
  have hzz := mul_conjugation_eq_one τ hτ (z : E) x₀ hx₀ hz
  have hφ : φ z * φ (conjugation F E z) = 1 := by rw [← map_mul, hzz, map_one]
  have hneg : ((-1 : K) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  -- the second component polynomial
  set lam : K := (-1) ^ n * φ (conjugation F E z) with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    have : lam * ((-1) ^ n * φ z) = 1 := by
      rw [hlam, show (-1 : K) ^ n * φ (conjugation F E z) * ((-1) ^ n * φ z) =
        ((-1) ^ n * (-1) ^ n) * (φ z * φ (conjugation F E z)) by ring, hneg, hφ, one_mul]
    rw [h, zero_mul] at this
    exact zero_ne_one this
  set g₂ : K[X] := C lam * g.reverse with hg₂_def
  have hg₂le (i : ℕ) (hi : i ≤ n) : g₂.coeff i = lam * g.coeff (n - i) := by
    rw [hg₂_def, coeff_C_mul, coeff_reverse, hgd, revAt_le hi]
  have hg₂gt (i : ℕ) (hi : n < i) : g₂.coeff i = 0 := by
    rw [hg₂_def, coeff_C_mul, coeff_reverse, hgd, revAt_eq_self_of_lt hi,
      coeff_eq_zero_of_natDegree_lt (hgd ▸ hi), mul_zero]
  have hg₂sep : g₂.Separable :=
    (separable_reverse hsep hgz).unit_mul (isUnit_C.mpr (IsUnit.mk0 _ hlam0))
  have hg₂a : aeval (↑u⁻¹ : K ⊗[E] B) g₂ = 0 := by
    have h := aeval_inv_reflect_mul_pow u g.natDegree g le_rfl
    rw [hua, hga] at h
    have h' : aeval (↑u⁻¹ : K ⊗[E] B) g.reverse = 0 := by
      have hu' : (u : K ⊗[E] B) ^ g.natDegree = ((u ^ g.natDegree : (K ⊗[E] B)ˣ) :
          K ⊗[E] B) := (Units.val_pow_eq_pow_val _ _).symm
      rw [← hua, hu'] at h
      exact (Units.mul_left_eq_zero _).mp h
    rw [hg₂_def, map_mul, h', mul_zero]
  -- the element
  obtain ⟨x, hx₁, hx₂⟩ := split_surjective K τ hτ a (↑u⁻¹ : K ⊗[E] B)
  -- the polynomial
  obtain ⟨ε, hε₁, hε₂⟩ := splitProj_surjective (F := F) (E := E) K 1 0
  let ι := algebraMap K (K ⊗[F] E)
  have hι (π : K ⊗[F] E →ₐ[K] K) (h : K[X]) : (h.map ι).map (π : K ⊗[F] E →+* K) = h := by
    rw [Polynomial.map_map, π.comp_algebraMap, Algebra.algebraMap_self, Polynomial.map_id]
  set f : (K ⊗[F] E)[X] := C ε * g.map ι + C (1 - ε) * g₂.map ι with hf_def
  have hf₁ : f.map (splitProj₁ F E K : K ⊗[F] E →+* K) = g := by
    rw [hf_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, hι, hι]
    change C (splitProj₁ F E K ε) * g + C (splitProj₁ F E K (1 - ε)) * g₂ = g
    rw [map_sub, map_one, hε₁, sub_self, map_one, map_zero, one_mul, zero_mul, add_zero]
  have hf₂ : f.map (splitProj₂ F E K : K ⊗[F] E →+* K) = g₂ := by
    rw [hf_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, hι, hι]
    change C (splitProj₂ F E K ε) * g + C (splitProj₂ F E K (1 - ε)) * g₂ = g₂
    rw [map_sub, map_one, hε₂, sub_zero, map_one, map_zero, one_mul, zero_mul, zero_add]
  have hc₁ (i : ℕ) : splitProj₁ F E K (f.coeff i) = g.coeff i := by
    rw [← hf₁, coeff_map]
    rfl
  have hc₂ (i : ℕ) : splitProj₂ F E K (f.coeff i) = g₂.coeff i := by
    rw [← hf₂, coeff_map]
    rfl
  have hp₁z : splitProj₁ F E K ((1 : K) ⊗ₜ[F] (z : E)) = φ z := by
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
    rfl
  have hp₂z : splitProj₂ F E K ((1 : K) ⊗ₜ[F] (z : E)) = φ (conjugation F E z) := by
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
    rfl
  have hcoeff_gt (i : ℕ) (hi : n < i) : f.coeff i = 0 := by
    apply splitProj_injective K
    · rw [hc₁, map_zero, coeff_eq_zero_of_natDegree_lt (hgd ▸ hi)]
    · rw [hc₂, map_zero, hg₂gt i hi]
  have hcoeff_n : f.coeff n = 1 := by
    apply splitProj_injective K
    · rw [hc₁, map_one, ← hgd, hgm.coeff_natDegree]
    · rw [hc₂, map_one, hg₂le n le_rfl, Nat.sub_self, hg0, hlam,
        show (-1 : K) ^ n * φ (conjugation F E z) * ((-1) ^ n * φ z) =
          ((-1) ^ n * (-1) ^ n) * (φ z * φ (conjugation F E z)) by ring, hneg, hφ, one_mul]
  have hL1 : (1 : K ⊗[F] E) ≠ 0 := by
    intro h
    have := congrArg (splitProj₁ F E K) h
    rw [map_one, map_zero] at this
    exact one_ne_zero this
  have hnat : f.natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hcoeff_gt)
      (by rw [hcoeff_n]; exact hL1)
  have hmon : f.Monic := by
    rw [Monic, leadingCoeff, hnat, hcoeff_n]
  refine ⟨x, f, ?_, hmon, hnat, ?_, ?_, ?_, ?_⟩
  · -- unitarity
    apply split_injective K τ hτ
    · rw [map_mul, hx₁, hx₂, map_one, ← hua, Units.mul_inv]
    · rw [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply, FirstKindInvolution.map_one,
        map_mul, hx₁, hx₂, map_one, ← hua, Units.mul_inv]
  · -- conjugate reciprocity
    intro i hi
    apply splitProj_injective K
    · rw [hc₁, map_mul, map_mul, map_pow, map_neg, map_one, hp₁z]
      erw [splitProj₁_centerConj]
      rw [hc₂, hg₂le i hi, hlam,
        show (-1 : K) ^ n * φ z * ((-1) ^ n * φ (conjugation F E z) * g.coeff (n - i)) =
          ((-1) ^ n * (-1) ^ n) * (φ z * φ (conjugation F E z)) * g.coeff (n - i) by ring,
        hneg, hφ, one_mul, one_mul]
    · rw [hc₂, map_mul, map_mul, map_pow, map_neg, map_one, hp₂z]
      erw [splitProj₂_centerConj]
      rw [hc₁, hg₂le (n - i) (Nat.sub_le n i), Nat.sub_sub_self hi, hlam]
  · -- `f(x) = 0`
    apply split_injective K τ hτ
    · rw [tensorQuotient_eval₂, hf₁, hx₁, hga, map_zero]
    · rw [tensorQuotient_baseChange_eval₂ K τ hτ, hf₂, hx₂, hg₂a,
        FirstKindInvolution.map_zero, map_zero]
  · -- `f'(x)` is a unit
    have hd₁ : (derivative f).map (splitProj₁ F E K : K ⊗[F] E →+* K) = derivative g := by
      rw [← derivative_map, hf₁]
    have hd₂ : (derivative f).map (splitProj₂ F E K : K ⊗[F] E →+* K) = derivative g₂ := by
      rw [← derivative_map, hf₂]
    have hu₁ : IsUnit (aeval a (derivative g)) := isUnit_aeval_derivative_of_separable hsep hga
    have hu₂ : IsUnit (aeval (↑u⁻¹ : K ⊗[E] B) (derivative g₂)) :=
      isUnit_aeval_derivative_of_separable hg₂sep hg₂a
    obtain ⟨w, hw₁, hw₂⟩ := split_surjective K τ hτ (↑hu₁.unit⁻¹ : K ⊗[E] B)
      (↑hu₂.unit⁻¹ : K ⊗[E] B)
    have hy₁ : q ((derivative f).eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) x) =
        aeval a (derivative g) := by
      rw [tensorQuotient_eval₂, hd₁, hx₁]
    have hy₂ : q (τ.baseChange K
        ((derivative f).eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) x)) =
        aeval (↑u⁻¹ : K ⊗[E] B) (derivative g₂) := by
      rw [tensorQuotient_baseChange_eval₂ K τ hτ, hd₂, hx₂]
    refine isUnit_iff_exists.mpr ⟨w, ?_, ?_⟩
    · apply split_injective K τ hτ
      · rw [map_mul, hy₁, hw₁, IsUnit.mul_val_inv, map_one]
      · rw [FirstKindInvolution.map_mul, map_mul, hw₂, hy₂, IsUnit.val_inv_mul,
          FirstKindInvolution.map_one, map_one]
    · apply split_injective K τ hτ
      · rw [map_mul, hy₁, hw₁, IsUnit.val_inv_mul, map_one]
      · rw [FirstKindInvolution.map_mul, map_mul, hw₂, hy₂, IsUnit.mul_val_inv,
          FirstKindInvolution.map_one, map_one]
  · -- independence of the powers
    intro c hc
    have h₁ : ∑ i, splitProj₁ F E K (c i) • a ^ (i : ℕ) = 0 := by
      have h := congrArg q hc
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, tensorQuotient_centerMap, hx₁, Algebra.smul_def]
    have h₂ : ∑ i, splitProj₂ F E K (c i) • (↑u⁻¹ : K ⊗[E] B) ^ (i : ℕ) = 0 := by
      have h := congrArg (fun y => q (τ.baseChange K y)) hc
      simp only [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensorQuotient_baseChange_centerMap_mul_pow K τ hτ, hx₂]
    have hk₁ := eq_zero_of_sum_smul_pow_eq_zero a hsep _ h₁
    have hk₂ := eq_zero_of_sum_smul_inv_pow_eq_zero u (by rw [hua]; exact hsep) _ h₂
    funext i
    apply splitProj_injective K
    · have h := congrFun hk₁ i
      simp only [Pi.zero_apply] at h
      rw [h, Pi.zero_apply, map_zero]
    · have h := congrFun hk₂ i
      simp only [Pi.zero_apply] at h
      rw [h, Pi.zero_apply, map_zero]

end SplitRegular

end Langlands.CentralSimple.UnitaryPoints
