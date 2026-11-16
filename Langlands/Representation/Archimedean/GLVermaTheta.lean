import Langlands.Representation.Archimedean.LowerVermaPBW
import Langlands.Representation.Archimedean.GLTensorLowest

/-!
# A trace functional on `Hom(W, M⁻(λ))`

Let `σ` be a representation of `𝔤𝔩_n(ℂ)` on `W` and `M⁻(λ)` the lower Verma module.

* `thetaU σ lam : U(𝔤𝔩_n) → End W` is the linear map defined on the ordered monomial basis
  `E^α = E^{α⁺} E^{α⁻}` (`VermaPBW.basisU`) by `E^α ↦ χ_λ(E^{α⁻}) σ(E^{α⁺})`, where `χ_λ` is the
  character of `U(𝔟⁻)` attached to `λ`. It satisfies `Θ(X u) = σ(X) Θ(u)` for `X ∈ 𝔫⁺` and
  `Θ(u Y) = μ_λ(Y) Θ(u)` for `Y ∈ 𝔟⁻`, so it descends to `theta σ lam : M⁻(λ) → End W` with
  `Θ(gen) = 1` and `Θ(X m) = σ(X) Θ(m)` for `X ∈ 𝔫⁺`.
* `lamFun σ lam y = (w ↦ tr (w' ↦ Θ(y w') w))` for `y ∈ Hom(W, M⁻(λ))`; it sends
  `ξ ⊗ gen` to `ξ` and kills `e_pq y` for `p < q` (cyclicity of the trace).
* `map_cas_of_upper`: a linear map killing the images of all `e_pq`, `p < q`, turns the Casimir
  operator on a weight vector of weight `μ` into multiplication by `casVal μ`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GLReynolds

open ComplexJacquetFinite Module Polynomial

/-! ### Functionals killing the raising operators -/

section Functional

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
  {n : ℕ} {h : Fin n → Fin n → Module.End ℂ Y}

/-- If `Λ` kills the images of all `e_pq` with `p < q`, then `Λ (c y) = casVal μ • Λ y` for a
weight vector `y` of weight `μ`. -/
theorem map_cas_of_upper (hh : IsGlFamily h) (Λ : Y →ₗ[ℂ] Z)
    (hΛ : ∀ p q, p < q → ∀ y, Λ (h p q y) = 0) {μ : Fin n → ℤ} {y : Y}
    (hy : IsWeightVec h μ y) : Λ (cas h y) = ((casVal μ : ℤ) : ℂ) • Λ y := by
  have hterm : ∀ p q, Λ ((h p q * h q p) y) =
      (((if p = q then μ p ^ 2 else 0) + (if q < p then μ p - μ q else 0) : ℤ) : ℂ) • Λ y := by
    intro p q
    rw [Module.End.mul_apply]
    rcases lt_trichotomy q p with hqp | rfl | hpq
    · have hrel := LinearMap.congr_fun (hh p q q p) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ite_true] at hrel
      have heq : h p q (h q p y) = h q p (h p q y) + (h p p y - h q q y) := by
        rw [← hrel]; abel
      rw [heq, map_add, hΛ q p hqp, zero_add, hy p, hy q, ← sub_smul, map_smul]
      simp [ne_of_gt hqp, hqp]
    · simp [hy q, smul_smul, sq]
    · rw [hΛ p q hpq]
      simp [ne_of_lt hpq, not_lt.mpr hpq.le]
  have hsum : ∑ p, ∑ q, ((if p = q then μ p ^ 2 else 0) + (if q < p then μ p - μ q else 0) : ℤ) =
      ∑ p, μ p ^ 2 + ∑ p, ∑ q, (if q < p then μ p - μ q else 0) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [cas, LinearMap.sum_apply, map_sum, hterm, ← Finset.sum_smul]
  congr 1
  rw [casVal, ← hsum]
  simp only [Int.cast_sum]

/-- `Λ (R(c) y) = R(casVal μ) • Λ y` for a weight vector `y` of weight `μ`. -/
theorem map_aeval_cas_of_upper (hh : IsGlFamily h) (Λ : Y →ₗ[ℂ] Z)
    (hΛ : ∀ p q, p < q → ∀ y, Λ (h p q y) = 0) {μ : Fin n → ℤ} {y : Y}
    (hy : IsWeightVec h μ y) (Q : ℂ[X]) :
    Λ (aeval (cas h) Q y) = Q.eval ((casVal μ : ℤ) : ℂ) • Λ y := by
  have hpow : ∀ k : ℕ, Λ ((cas h ^ k) y) = (((casVal μ : ℤ) : ℂ) ^ k) • Λ y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hw : IsWeightVec h μ ((cas h ^ k) y) := by
        have := isWeightVec_aeval_cas hh (X ^ k) hy
        simpa using this
      rw [map_cas_of_upper hh Λ hΛ hw, ih, smul_smul, pow_succ', mul_comm]
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, map_add, hP, hQ, eval_add, add_smul]
  | monomial k c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow,
      eval_monomial, smul_smul, mul_comm]

end Functional

/-! ### The map `Θ : U(𝔤𝔩_n) → End W` -/

section Theta

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W) (lam : Fin n → ℂ)

/-- The extension of `σ|𝔫⁺` to `U(𝔫⁺)`. -/
def sigU : UniversalEnvelopingAlgebra ℂ (VermaPBW.nUp n) →ₐ[ℂ] Module.End ℂ W :=
  UniversalEnvelopingAlgebra.lift ℂ (σ.comp (VermaPBW.nUp n).incl)

theorem sigU_ι (X : VermaPBW.nUp n) :
    sigU σ (UniversalEnvelopingAlgebra.ι ℂ X) = σ (X : Matrix (Fin n) (Fin n) ℂ) := by
  rw [sigU, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The character `χ_λ` of `U(𝔟⁻)`. -/
abbrev chiL : UniversalEnvelopingAlgebra ℂ (VermaPBW.bLo n) →ₐ[ℂ] ℂ :=
  VermaPBW.subChar n _ (VermaPBW.lo_trans n) (VermaPBW.muLo n lam)

/-- The value `χ_λ(E^{α⁻}) σ(E^{α⁺})` on the ordered monomial `E^α`. -/
def thetaVal (α : VermaPBW.Idx n →₀ ℕ) : Module.End ℂ W :=
  chiL lam (VermaPBW.monoLo n (α.subtypeDomain fun c => ¬ c.1 < c.2)) •
    sigU σ (VermaPBW.monoUp n (α.subtypeDomain fun c => c.1 < c.2))

/-- The linear map `Θ : U(𝔤𝔩_n) → End W`, `E^α ↦ χ_λ(E^{α⁻}) σ(E^{α⁺})`. -/
def thetaU : VermaGL.glU n →ₗ[ℂ] Module.End ℂ W :=
  (VermaPBW.basisU n).constr ℂ (thetaVal σ lam)

theorem thetaU_mono (β : VermaPBW.UpIdx n →₀ ℕ) (γ : VermaPBW.LoIdx n →₀ ℕ) :
    thetaU σ lam (VermaPBW.subInc n _ (VermaPBW.up_trans n) (VermaPBW.monoUp n β) *
        VermaPBW.subInc n _ (VermaPBW.lo_trans n) (VermaPBW.monoLo n γ)) =
      chiL lam (VermaPBW.monoLo n γ) • sigU σ (VermaPBW.monoUp n β) := by
  classical
  let α : VermaPBW.Idx n →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun c => if h : c.1 < c.2 then β ⟨c, h⟩ else γ ⟨c, h⟩)
  have h1 : α.subtypeDomain (fun c => c.1 < c.2) = β := by
    ext c
    simp [α, c.2]
  have h2 : α.subtypeDomain (fun c => ¬ c.1 < c.2) = γ := by
    ext c
    simp [α, c.2]
  have hα := VermaPBW.basisU_eq_subInc n α
  rw [h1, h2] at hα
  rw [← hα, thetaU, Module.Basis.constr_basis, thetaVal, h1, h2]

/-- `Θ(u u') = χ_λ(u') σ(u)` for `u ∈ U(𝔫⁺)` and `u' ∈ U(𝔟⁻)`. -/
theorem thetaU_subInc_mul (u : UniversalEnvelopingAlgebra ℂ (VermaPBW.nUp n))
    (u' : UniversalEnvelopingAlgebra ℂ (VermaPBW.bLo n)) :
    thetaU σ lam (VermaPBW.subInc n _ (VermaPBW.up_trans n) u *
        VermaPBW.subInc n _ (VermaPBW.lo_trans n) u') = chiL lam u' • sigU σ u := by
  have h1 : ∀ β : VermaPBW.UpIdx n →₀ ℕ, ∀ u' : UniversalEnvelopingAlgebra ℂ (VermaPBW.bLo n),
      thetaU σ lam (VermaPBW.subInc n _ (VermaPBW.up_trans n) (VermaPBW.monoUp n β) *
        VermaPBW.subInc n _ (VermaPBW.lo_trans n) u') =
        chiL lam u' • sigU σ (VermaPBW.monoUp n β) := by
    intro β
    have := LinearMap.ext_on_range (VermaPBW.span_monoLo n)
      (f := thetaU σ lam ∘ₗ LinearMap.mulLeft ℂ
          (VermaPBW.subInc n _ (VermaPBW.up_trans n) (VermaPBW.monoUp n β)) ∘ₗ
        (VermaPBW.subInc n _ (VermaPBW.lo_trans n)).toLinearMap)
      (g := (chiL lam).toLinearMap.smulRight (sigU σ (VermaPBW.monoUp n β)))
      (fun γ => by
        simpa using thetaU_mono σ lam β γ)
    exact fun u' => by simpa using LinearMap.congr_fun this u'
  have := LinearMap.ext_on_range (VermaPBW.span_monoUp n)
    (f := thetaU σ lam ∘ₗ LinearMap.mulRight ℂ (VermaPBW.subInc n _ (VermaPBW.lo_trans n) u') ∘ₗ
      (VermaPBW.subInc n _ (VermaPBW.up_trans n)).toLinearMap)
    (g := chiL lam u' • (sigU σ).toLinearMap)
    (fun β => by
      simpa using h1 β u')
  simpa using LinearMap.congr_fun this u

/-- Left `𝔫⁺`-equivariance: `Θ(X u) = σ(X) Θ(u)`. -/
theorem thetaU_ι_mul (X : VermaPBW.nUp n) (u : VermaGL.glU n) :
    thetaU σ lam (UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ) * u) =
      σ (X : Matrix (Fin n) (Fin n) ℂ) * thetaU σ lam u := by
  have := (VermaPBW.basisU n).ext (f₁ := thetaU σ lam ∘ₗ LinearMap.mulLeft ℂ
      (UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ)))
    (f₂ := LinearMap.mulLeft ℂ (σ (X : Matrix (Fin n) (Fin n) ℂ)) ∘ₗ thetaU σ lam) (fun α => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      rw [VermaPBW.basisU_eq_subInc, ← mul_assoc, ← VermaPBW.subInc_ι n _ (VermaPBW.up_trans n) X,
        ← map_mul, thetaU_subInc_mul, thetaU_subInc_mul, map_mul, sigU_ι, mul_smul_comm])
  simpa using LinearMap.congr_fun this u

/-- Right `𝔟⁻`-equivariance: `Θ(u Y) = μ_λ(Y) Θ(u)`. -/
theorem thetaU_mul_ι (Y : VermaPBW.bLo n) (u : VermaGL.glU n) :
    thetaU σ lam (u * UniversalEnvelopingAlgebra.ι ℂ (Y : Matrix (Fin n) (Fin n) ℂ)) =
      VermaPBW.muLo n lam Y • thetaU σ lam u := by
  have := (VermaPBW.basisU n).ext (f₁ := thetaU σ lam ∘ₗ LinearMap.mulRight ℂ
      (UniversalEnvelopingAlgebra.ι ℂ (Y : Matrix (Fin n) (Fin n) ℂ)))
    (f₂ := VermaPBW.muLo n lam Y • thetaU σ lam) (fun α => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        LinearMap.smul_apply]
      rw [VermaPBW.basisU_eq_subInc, mul_assoc, ← VermaPBW.subInc_ι n _ (VermaPBW.lo_trans n) Y,
        ← map_mul, thetaU_subInc_mul, thetaU_subInc_mul, map_mul, VermaPBW.subChar_ι, mul_comm,
        mul_smul])
  simpa using LinearMap.congr_fun this u

theorem thetaU_mul_unitE_lo (c : VermaPBW.LoIdx n) (u : VermaGL.glU n) :
    thetaU σ lam (u * UniversalEnvelopingAlgebra.ι ℂ (VermaPBW.unitE n c.1)) =
      VermaPBW.vVal n lam 0 c.1 • thetaU σ lam u := by
  have h := thetaU_mul_ι σ lam (VermaPBW.subBasis n _ (VermaPBW.lo_trans n) c) u
  rwa [VermaPBW.coe_subBasis, VermaPBW.muLo_subBasis n 0 lam] at h

/-- `Θ` vanishes on `U · x` for `x` in the defining left ideal of `M⁻(λ)`. -/
theorem thetaU_mul_mem {x : VermaGL.glU n} (hx : x ∈ VermaGL.lowerVermaIdeal n lam)
    (u : VermaGL.glU n) : thetaU σ lam (u * x) = 0 := by
  induction hx using Submodule.span_induction generalizing u with
  | mem x hx =>
    rcases hx with ⟨p, q, hqp, rfl⟩ | ⟨p, rfl⟩
    · have h := thetaU_mul_unitE_lo σ lam ⟨(p, q), not_lt.mpr hqp.le⟩ u
      rw [VermaPBW.vVal_of_lt n lam 0 hqp, zero_smul] at h
      exact h
    · have h := thetaU_mul_unitE_lo σ lam ⟨(p, p), lt_irrefl p⟩ u
      rw [VermaPBW.vVal_diag] at h
      rw [mul_sub, map_sub, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
      exact sub_eq_zero.mpr h
  | zero => rw [mul_zero, map_zero]
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, ← mul_assoc]; exact hx _

theorem thetaU_one : thetaU σ lam 1 = 1 := by
  have h := thetaU_subInc_mul σ lam 1 1
  simpa only [map_one, one_mul, one_smul] using h

/-- `Θ` descends to `M⁻(λ)`. -/
def theta : VermaGL.LowerVerma n lam →ₗ[ℂ] Module.End ℂ W :=
  ((VermaGL.lowerVermaIdeal n lam).restrictScalars ℂ).liftQ (thetaU σ lam)
      (fun x hx => by
        have h := thetaU_mul_mem σ lam hx 1
        rwa [one_mul] at h) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (VermaGL.lowerVermaIdeal n lam)).symm.toLinearMap

theorem theta_mk (u : VermaGL.glU n) :
    theta σ lam (Submodule.Quotient.mk u) = thetaU σ lam u := by
  simp only [theta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  rfl

theorem theta_gen : theta σ lam (VermaGL.gen n lam) = 1 := by
  rw [VermaGL.gen, theta_mk, thetaU_one]

/-- `Θ(X m) = σ(X) Θ(m)` for `X ∈ 𝔫⁺`. -/
theorem theta_action (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ VermaPBW.nUp n)
    (m : VermaGL.LowerVerma n lam) :
    theta σ lam (VermaGL.action n lam X m) = σ X * theta σ lam m := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change theta σ lam (UniversalEnvelopingAlgebra.ι ℂ X • Submodule.Quotient.mk u) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, theta_mk, theta_mk]
  exact thetaU_ι_mul σ lam ⟨X, hX⟩ u

theorem single_mem_nUp {p q : Fin n} (hpq : p < q) :
    Matrix.single p q (1 : ℂ) ∈ VermaPBW.nUp n := by
  have h := VermaPBW.unitE_mem_subalg n (fun i j => i < j) (VermaPBW.up_trans n)
    ⟨(p, q), hpq⟩
  exact h

end Theta

/-! ### The trace functional -/

section Trace

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W) (lam : Fin n → ℂ)

/-- `Λ(y) = (w ↦ tr (w' ↦ Θ(y w') w))` on `Hom(W, M⁻(λ))`. -/
def lamFun : (W →ₗ[ℂ] VermaGL.LowerVerma n lam) →ₗ[ℂ] (W →ₗ[ℂ] ℂ) where
  toFun y := LinearMap.trace ℂ W ∘ₗ (theta σ lam ∘ₗ y).flip
  map_add' y y' := by
    ext w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
    rw [← map_add]
    congr 1
    ext w'
    simp
  map_smul' c y := by
    ext w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    ext w'
    simp

theorem lamFun_apply (y : W →ₗ[ℂ] VermaGL.LowerVerma n lam) (w : W) :
    lamFun σ lam y w = LinearMap.trace ℂ W ((theta σ lam ∘ₗ y).flip w) := rfl

/-- `Λ(ξ ⊗ gen) = ξ`. -/
theorem lamFun_smulRight_gen [FiniteDimensional ℂ W] (ξ : W →ₗ[ℂ] ℂ) :
    lamFun σ lam (ξ.smulRight (VermaGL.gen n lam)) = ξ := by
  ext w
  rw [lamFun_apply]
  have h : (theta σ lam ∘ₗ ξ.smulRight (VermaGL.gen n lam)).flip w = ξ.smulRight w := by
    ext w'
    simp [theta_gen]
  rw [h, LinearMap.trace_smulRight]

/-- `Λ` kills `e_pq y` for `p < q`. -/
theorem lamFun_homFam (p q : Fin n) (hpq : p < q) (y : W →ₗ[ℂ] VermaGL.LowerVerma n lam) :
    lamFun σ lam (homFam (famOf σ) (famOf (VermaGL.action n lam)) p q y) = 0 := by
  ext w
  rw [lamFun_apply, LinearMap.zero_apply]
  set G : Module.End ℂ W := (theta σ lam ∘ₗ y).flip w
  have h : (theta σ lam ∘ₗ homFam (famOf σ) (famOf (VermaGL.action n lam)) p q y).flip w =
      σ (Matrix.single p q 1) * G - G * σ (Matrix.single p q 1) := by
    ext w'
    simp only [LinearMap.flip_apply, LinearMap.coe_comp, Function.comp_apply, homFam_apply,
      famOf_apply, map_sub, LinearMap.sub_apply, Module.End.mul_apply, G]
    rw [theta_action σ lam _ (single_mem_nUp hpq), Module.End.mul_apply]
  rw [h, map_sub, LinearMap.trace_mul_comm, sub_self]

/-- For `y` of weight `μ`, `Λ (R(c) y) = R(casVal μ) Λ y`. -/
theorem lamFun_aeval_cas {μ : Fin n → ℤ} {y : W →ₗ[ℂ] VermaGL.LowerVerma n lam}
    (hy : IsWeightVec (homFam (famOf σ) (famOf (VermaGL.action n lam))) μ y) (Q : ℂ[X]) :
    lamFun σ lam (aeval (cas (homFam (famOf σ) (famOf (VermaGL.action n lam)))) Q y) =
      Q.eval ((casVal μ : ℤ) : ℂ) • lamFun σ lam y :=
  map_aeval_cas_of_upper (isGlFamily_homFam (isGlFamily_famOf σ) (isGlFamily_famOf _))
    (lamFun σ lam) (fun p q hpq y => lamFun_homFam σ lam p q hpq y) hy Q

end Trace

end GLReynolds

end Langlands.Archimedean
