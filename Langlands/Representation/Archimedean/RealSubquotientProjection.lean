import Langlands.Representation.Archimedean.RealSubquotientEval
import Langlands.Representation.Archimedean.Kostant.Center
import Langlands.Representation.Archimedean.Kostant.RealTransfer
import Langlands.Representation.Archimedean.Kostant.Assembly
import Langlands.Representation.Archimedean.JacquetFunctionalCenter
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The principal-series projection of `U(𝔤) ⊗ ℂ^d`

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).
Fix a continuous matrix representation `τ` of `O(n)` on `ℂ^d` with derivative `D`.

* `realSymbol`: symbols of `U(ℂ ⊗ 𝔤𝔩_n(ℝ))`, transported from `𝔤𝔩_n(ℂ)` (`Kostant.glSymbol`);
  `diagRes` restricts a symbol to the diagonal matrices.
* `lam_ι_mul`: for a `K`-intertwiner `T` from `τ` into the principal series of `chars a e`,
  `(R(x u) T v)(1) = ℓ_a(x) (R(u) T v)(1) + (R([x_k, u]) T v)(1) + (R(u) T (D(x_k) v))(1)`, where
  `x = x_b + x_k` is the decomposition into an upper triangular and an antisymmetric part.
* `Q`: the polynomial vector `Q(u, v) ∈ ℂ[a]^d` with `(R(u) T v)(1) = (T (Q(u,v)(a)))(1)` for
  all `a`, `e` and all such `T` (`Q_represents`); it is unique (`Represents.unique`, `Q_eq`), of
  degree at most `m` on the `m`-th filtration piece, with degree-`m` part the diagonal
  restriction of the symbol (`Q_degree`).
* `act`: the action `(b · T)(eᵢ) = ∑ⱼ P(bᵢⱼ) T(eⱼ)` of matrices over `U(𝔤)` on linear maps
  `ℂ^d → M`; `InB τ b`: `b` is `K`-invariant; `act_mem`: `K`-invariant matrices preserve
  `K`-intertwiners.
* `chat τ b`: the matrix of polynomials `ĉ(b)` with `((b · T) x)(1) = (T (ĉ(b)(a) x))(1)` on every
  principal series (`eval_one_act_psAct`); `chat_mul`: `ĉ(b b') = ĉ(b') ĉ(b)` for `K`-invariant
  `b'`.
* `exists_Q_central`: a central element `z` acts through a scalar polynomial `ξ`,
  `Q(z, v) = ξ v`; it rests on `exists_sub_mem_Jideal` (`z` is a scalar modulo the space `J_a`
  spanned by the `x u - ℓ_a(x) u`, `x` upper triangular).
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

open Langlands.LocalFactor.Archimedean RealJacquetFrobenius Kostant MvPolynomial
open Langlands.Algebra.UniversalEnveloping InfinitesimalCharacter

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The universal enveloping algebra of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
abbrev UU (n : ℕ) := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)

/-- The real Lie algebra `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
abbrev LL (n : ℕ) := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ

/-! ## Symbols -/

/-- The symbol data of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, transported from `𝔤𝔩_n(ℂ)` along `toGL`. -/
def realSymbol (n : ℕ) : SymbolData ℂ (LL n)
    (AssocSymbol.CoordRing ℂ (B := Coord (fun _ : Unit => n)))
    (AssocSymbol.SymRing ℂ (B := Coord (fun _ : Unit => n))) where
  ρ := (glSymbol ℂ (fun _ : Unit => n)).ρ.comp (toGL n).toLieHom
  leibniz _ := (glSymbol ℂ (fun _ : Unit => n)).leibniz _
  𝔪 := (glSymbol ℂ (fun _ : Unit => n)).𝔪
  ε := (glSymbol ℂ (fun _ : Unit => n)).ε
  ε_eq_zero := (glSymbol ℂ (fun _ : Unit => n)).ε_eq_zero
  l := (glSymbol ℂ (fun _ : Unit => n)).l
  l_mem := (glSymbol ℂ (fun _ : Unit => n)).l_mem

theorem realSymbol_ξ (x : LL n) :
    (realSymbol n).ξ x = (glSymbol ℂ (fun _ : Unit => n)).ξ (toGL n x) :=
  rfl

theorem realSymbol_ξ_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    (realSymbol n).ξ (z ⊗ₜ X) =
      ∑ c : Coord (fun _ : Unit => n), (z * (X c.2.1 c.2.2 : ℂ)) • (MvPolynomial.X c) := by
  rw [realSymbol_ξ, AssocSymbol.symbolData_ξ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [glBasis_repr, toGL_tmul]
  simp [Matrix.smul_apply, Matrix.map_apply]

/-- Restriction of a polynomial on `𝔤𝔩_n(ℂ)` to the diagonal matrices `diag(x)`. -/
def diagRes (n : ℕ) :
    MvPolynomial (Coord (fun _ : Unit => n)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval fun c => if c.2.1 = c.2.2 then X c.2.1 else 0

/-- The linear form `x ↦ ∑ₚ x_pp X_p` attached to `x ∈ 𝔤`: the restriction of its symbol to the
diagonal. -/
def diagLin (x : LL n) : MvPolynomial (Fin n) ℂ := diagRes n ((realSymbol n).ξ x)

theorem diagLin_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    diagLin (z ⊗ₜ X) = ∑ p, C (z * (X p p : ℂ)) * MvPolynomial.X p := by
  rw [diagLin, realSymbol_ξ_tmul, map_sum]
  simp only [map_smul, diagRes, aeval_X]
  rw [Fintype.sum_sigma]
  simp only [Fintype.univ_unit, Finset.sum_singleton]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single p]
  · simp [smul_eq_C_mul]
  · intro q _ hqp
    simp [Ne.symm hqp]
  · simp

theorem diagLin_add (x y : LL n) : diagLin (x + y) = diagLin x + diagLin y := by
  simp [diagLin, map_add]

theorem diagLin_smul (c : ℂ) (x : LL n) : diagLin (c • x) = C c * diagLin x := by
  simp [diagLin, map_smul, smul_eq_C_mul]

theorem diagLin_isHomogeneous (x : LL n) : (diagLin x).IsHomogeneous 1 := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [diagLin_tmul]
    refine IsHomogeneous.sum _ _ _ fun p _ => ?_
    simpa using (isHomogeneous_C (Fin n) (z * (X p p : ℂ))).mul (isHomogeneous_X ℂ p)
  | add x y hx hy =>
    rw [diagLin_add]
    exact hx.add hy

theorem eval_diagLin_tmul (a : Fin n → ℂ) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    eval a (diagLin (z ⊗ₜ X)) = z * ∑ j, a j * (X j j : ℂ) := by
  rw [diagLin_tmul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul, eval_C, eval_X]
  ring

/-! ## The decomposition `𝔤 = 𝔟 + 𝔨` -/

/-- The upper triangular part, extended complex-linearly to `ℂ ⊗ 𝔤𝔩_n(ℝ)`. -/
def upL (n : ℕ) : LL n →ₗ[ℂ] LL n :=
  (RealJacquetFrobenius.upperPart : Matrix (Fin n) (Fin n) ℝ →L[ℝ] _).toLinearMap.baseChange ℂ

/-- The antisymmetric part, extended complex-linearly to `ℂ ⊗ 𝔤𝔩_n(ℝ)`. -/
def skL (n : ℕ) : LL n →ₗ[ℂ] LL n :=
  (RealJacquetFrobenius.skewPart : Matrix (Fin n) (Fin n) ℝ →L[ℝ] _).toLinearMap.baseChange ℂ

theorem upL_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    upL n (z ⊗ₜ X) = z ⊗ₜ RealJacquetFrobenius.upperPart X := rfl

theorem skL_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    skL n (z ⊗ₜ X) = z ⊗ₜ RealJacquetFrobenius.skewPart X := rfl

theorem upL_add_skL (x : LL n) : upL n x + skL n x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [upL_tmul, skL_tmul, ← TensorProduct.tmul_add, RealJacquetFrobenius.upperPart_add_skewPart]
  | add x y hx hy => rw [map_add, map_add, add_add_add_comm, hx, hy]

theorem upperPart_diag (X : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    RealJacquetFrobenius.upperPart X j j = X j j := by
  change X j j - RealJacquetFrobenius.skewPart X j j = X j j
  simp [RealJacquetFrobenius.skewPart_apply]

theorem skewPart_transpose (X : Matrix (Fin n) (Fin n) ℝ) :
    (RealJacquetFrobenius.skewPart X)ᵀ = -RealJacquetFrobenius.skewPart X := by
  have h := RealJacquetFrobenius.skewPart_mem X
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- The complex-linear extension of `D` to `ℂ ⊗ 𝔤𝔩_n(ℝ)`. -/
def Dc {d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ) :
    LL n →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton ℂ _ D)

theorem Dc_tmul {d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ) (z : ℂ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Dc D (z ⊗ₜ X) = z • D X := by
  simp [Dc]

/-- On the principal series, the upper triangular part acts on evaluation at `1` by the
character `ℓ_a(x) = ∑ⱼ aⱼ xⱼⱼ`. -/
theorem eval_one_upL (a : Fin n → ℂ) (e : Fin n → Fin 2) (x : LL n) (G : PS a e) :
    ((realStandardLie n (psList a e) (upL n x) G : PS a e) :
        Langlands.GeneralLinear n ℝ → ℂ) 1 =
      eval a (diagLin x) * (G : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
  have hG : (G : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n (posChar a e) :=
    realStandardModule_le_principalSeries n (psList a e) G.2.1
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] RealJacquetFrobenius.upperPart X =
        z • ((1 : ℂ) ⊗ₜ[ℝ] RealJacquetFrobenius.upperPart X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [upL_tmul, hz, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      realStandardLie_one_tmul_apply_coe,
      rightDerivative_upper_apply_one hG (RealJacquetFrobenius.upperPart_isUpperTriangular X),
      eval_diagLin_tmul, smul_eq_mul]
    simp only [upperPart_diag]
    ring
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy,
      diagLin_add, map_add, add_mul]

/-- A `K`-intertwiner from `τ` into a `(𝔤𝔩_n(ℝ), O(n))`-module carries the action of the
antisymmetric part to `D`. -/
theorem apply_skL_intertwiner {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} (hgk : IsRealGKModule n ρ π)
    {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ} (hD : IsTypeDerivative τ D)
    {T : (Fin d → ℂ) →ₗ[ℂ] V} (hT : T ∈ gkIntertwiners ρ d τ) (x : LL n) (v : Fin d → ℂ) :
    π (skL n x) (T v) = T (Dc D (skL n x) *ᵥ v) := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] RealJacquetFrobenius.skewPart X =
        z • ((1 : ℂ) ⊗ₜ[ℝ] RealJacquetFrobenius.skewPart X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [skL_tmul, Dc_tmul, hz, map_smul, LinearMap.smul_apply,
      apply_skew_intertwiner hgk hD hT _ (skewPart_transpose X), Matrix.smul_mulVec,
      map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, Matrix.add_mulVec, map_add]

/-! ## Evaluation at the identity of the enveloping action -/

/-- The action of `U(𝔤)` on the `O(n)`-finite principal series of `chars a e`. -/
abbrev psAct (a : Fin n → ℂ) (e : Fin n → Fin 2) : UU n →ₐ[ℂ] Module.End ℂ (PS a e) :=
  envelopingAction (realStandardLie n (psList a e))

/-- `λ_T(u, v) = (R(u) T v)(1)`. -/
def lam (a : Fin n → ℂ) (e : Fin n → Fin 2) {d : ℕ} (T : (Fin d → ℂ) →ₗ[ℂ] PS a e) (u : UU n)
    (v : Fin d → ℂ) : ℂ :=
  ((psAct a e u (T v) : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1

section Lam

variable {a : Fin n → ℂ} {e : Fin n → Fin 2} {d : ℕ} (T : (Fin d → ℂ) →ₗ[ℂ] PS a e)

theorem lam_add (u u' : UU n) (v : Fin d → ℂ) : lam a e T (u + u') v = lam a e T u v + lam a e T u' v := by
  simp [lam]

theorem lam_smul (c : ℂ) (u : UU n) (v : Fin d → ℂ) : lam a e T (c • u) v = c * lam a e T u v := by
  simp [lam]

theorem lam_sub (u u' : UU n) (v : Fin d → ℂ) : lam a e T (u - u') v = lam a e T u v - lam a e T u' v := by
  simp [lam]

theorem lam_zero (v : Fin d → ℂ) : lam a e T 0 v = 0 := by
  simp [lam]

theorem lam_one (v : Fin d → ℂ) :
    lam a e T 1 v = ((T v : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
  simp [lam]

theorem psAct_ι (x : LL n) : psAct a e (UniversalEnvelopingAlgebra.ι ℂ x) = realStandardLie n (psList a e) x := by
  simp [psAct, envelopingAction]

/-- The recursion for `λ_T` along a generator. -/
theorem lam_ι_mul {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ} (hD : IsTypeDerivative τ D)
    (hT : T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ) (x : LL n) (u : UU n)
    (v : Fin d → ℂ) :
    lam a e T (UniversalEnvelopingAlgebra.ι ℂ x * u) v =
      eval a (diagLin x) * lam a e T u v +
        lam a e T (UniversalEnvelopingAlgebra.ι ℂ (skL n x) * u -
          u * UniversalEnvelopingAlgebra.ι ℂ (skL n x)) v +
        lam a e T u (Dc D (skL n x) *ᵥ v) := by
  have hx : UniversalEnvelopingAlgebra.ι ℂ x = UniversalEnvelopingAlgebra.ι ℂ (upL n x) +
      UniversalEnvelopingAlgebra.ι ℂ (skL n x) := by
    rw [← map_add, upL_add_skL]
  have hsk := apply_skL_intertwiner (isRealGKModule_realStandardModule n (psList a e)) hD hT x v
  simp only [lam]
  rw [hx, add_mul, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, map_mul,
    Module.End.mul_apply, psAct_ι, eval_one_upL]
  simp only [map_sub, map_mul, Module.End.mul_apply, psAct_ι, LinearMap.sub_apply, hsk,
    Submodule.coe_sub, Pi.sub_apply]
  ring

end Lam

/-! ## The polynomial representative -/

variable {d : ℕ}

/-- Evaluation of a polynomial vector at `a`. -/
def evalVec (a : Fin n → ℂ) (q : Fin d → MvPolynomial (Fin n) ℂ) : Fin d → ℂ :=
  fun i => eval a (q i)

theorem evalVec_add (a : Fin n → ℂ) (q q' : Fin d → MvPolynomial (Fin n) ℂ) :
    evalVec a (q + q') = evalVec a q + evalVec a q' := by
  funext i; simp [evalVec]

theorem evalVec_smul (a : Fin n → ℂ) (c : ℂ) (q : Fin d → MvPolynomial (Fin n) ℂ) :
    evalVec a (fun i => C c * q i) = c • evalVec a q := by
  funext i; simp [evalVec]

variable (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)

/-- `q` represents `(u, v)`: `(R(u) T v)(1) = (T (q(a)))(1)` for all `a`, `e` and every
`K`-intertwiner `T` from `τ` into the principal series of `chars a e`. -/
def Represents (u : UU n) (v : Fin d → ℂ) (q : Fin d → MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ (a : Fin n → ℂ) (e : Fin n → Fin 2) (T : (Fin d → ℂ) →ₗ[ℂ] PS a e),
    T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ →
      lam a e T u v = ((T (evalVec a q) : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1

variable {τ}

theorem Represents.add {u u' : UU n} {v : Fin d → ℂ} {q q' : Fin d → MvPolynomial (Fin n) ℂ}
    (h : Represents τ u v q) (h' : Represents τ u' v q') : Represents τ (u + u') v (q + q') := by
  intro a e T hT
  rw [lam_add, h a e T hT, h' a e T hT, evalVec_add, map_add, Submodule.coe_add, Pi.add_apply]

theorem Represents.smul {u : UU n} {v : Fin d → ℂ} {q : Fin d → MvPolynomial (Fin n) ℂ}
    (c : ℂ) (h : Represents τ u v q) : Represents τ (c • u) v (fun i => C c * q i) := by
  intro a e T hT
  rw [lam_smul, h a e T hT, evalVec_smul, map_smul, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul]

theorem represents_zero (v : Fin d → ℂ) : Represents τ 0 v 0 := by
  intro a e T hT
  have : evalVec a (0 : Fin d → MvPolynomial (Fin n) ℂ) = 0 := by funext i; simp [evalVec]
  rw [lam_zero, this, map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]

/-- Polynomial representatives exist, with degree at most `m` on words of length at most `m`,
and with degree-`m` part `diagRes(σ_m(u)) v`. -/
theorem exists_represents {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
    (hD : IsTypeDerivative τ D) :
    ∀ (m : ℕ), ∀ u ∈ Kostant.wordSpan ℂ (LL n) m, ∀ v : Fin d → ℂ,
      ∃ q : Fin d → MvPolynomial (Fin n) ℂ, (∀ i, (q i).totalDegree ≤ m) ∧
        (∀ i, homogeneousComponent m (q i) =
          diagRes n ((realSymbol n).symbol m u) * C (v i)) ∧ Represents τ u v q := by
  intro m
  induction m with
  | zero =>
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      have hl0 : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      subst hl0
      intro v
      refine ⟨fun i => C (v i), fun i => by simp, fun i => ?_, ?_⟩
      · have h : (realSymbol n).symbol 0 (1 : UU n) = 1 := by
          simpa using (realSymbol n).symbol_zero_algebraMap 1
        rw [word_nil, h, map_one, one_mul, homogeneousComponent_zero, coeff_zero_C]
      · intro a e T hT
        have : evalVec a (fun i => C (v i)) = v := by funext i; simp [evalVec]
        rw [this, word_nil, lam_one]
    | zero =>
      intro v
      exact ⟨0, fun i => by simp, fun i => by simp, represents_zero v⟩
    | add u u' _ _ hu hu' =>
      intro v
      obtain ⟨q, hq1, hq2, hq3⟩ := hu v
      obtain ⟨q', hq1', hq2', hq3'⟩ := hu' v
      refine ⟨q + q', fun i => ?_, fun i => ?_, hq3.add hq3'⟩
      · exact (totalDegree_add _ _).trans (max_le (hq1 i) (hq1' i))
      · rw [Pi.add_apply, map_add, hq2 i, hq2' i, map_add, map_add, add_mul]
    | smul c u _ hu =>
      intro v
      obtain ⟨q, hq1, hq2, hq3⟩ := hu v
      refine ⟨fun i => C c * q i, fun i => ?_, fun i => ?_, hq3.smul c⟩
      · exact (totalDegree_mul _ _).trans (by simp [hq1 i])
      · rw [show (fun i => C c * q i) i = c • q i from (smul_eq_C_mul _ _).symm, map_smul,
          hq2 i, map_smul, map_smul, smul_eq_C_mul, smul_eq_C_mul]
        ring
  | succ m ih =>
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      intro v
      rcases Nat.lt_or_ge l.length (m + 1) with hlt | hge
      · obtain ⟨q, hq1, hq2, hq3⟩ := ih (word ℂ (LL n) l)
          (Kostant.word_mem_wordSpan ℂ (LL n) l (by omega)) v
        refine ⟨q, fun i => (hq1 i).trans (Nat.le_succ m), fun i => ?_, hq3⟩
        rw [(realSymbol n).symbol_word_of_length_lt l hlt, map_zero, zero_mul]
        exact homogeneousComponent_eq_zero _ _ (by have := hq1 i; omega)
      · obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
          cases l with
          | nil => simp at hge
          | cons x l' => exact ⟨x, l', rfl⟩
        have hl' : l'.length = m := by simp at hl hge; omega
        set w := word ℂ (LL n) l' with hw
        have hwF : w ∈ degreeFiltration ℂ (LL n) m := by
          rw [hw, ← hl']; exact word_mem_degreeFiltration ℂ (LL n) l'
        have hwS : w ∈ Kostant.wordSpan ℂ (LL n) m := degreeFiltration_le_wordSpan ℂ (LL n) m hwF
        have hι : UniversalEnvelopingAlgebra.ι ℂ (skL n x) ∈ degreeFiltration ℂ (LL n) 1 := by
          rw [degreeFiltration_one]; exact generator_mem_degreeOne ℂ (LL n) _
        have hcF := commutator_mem_degreeFiltration ℂ (LL n) hι hwF
        rw [show 1 + m - 1 = m by omega] at hcF
        have hcS := degreeFiltration_le_wordSpan ℂ (LL n) m hcF
        obtain ⟨q1, h11, h12, h13⟩ := ih w hwS v
        obtain ⟨q2, h21, h22, h23⟩ := ih _ hcS v
        obtain ⟨q3, h31, h32, h33⟩ := ih w hwS (Dc D (skL n x) *ᵥ v)
        refine ⟨fun i => diagLin x * q1 i + q2 i + q3 i, fun i => ?_, fun i => ?_, ?_⟩
        · refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
            (max_le ((totalDegree_mul _ _).trans ?_) ((h21 i).trans (Nat.le_succ m))))
            ((h31 i).trans (Nat.le_succ m)))
          have := (diagLin_isHomogeneous x).totalDegree_le
          have := h11 i
          omega
        · have hsym : (realSymbol n).symbol (m + 1) (word ℂ (LL n) (x :: l')) =
              (realSymbol n).ξ x * (realSymbol n).symbol m w := by
            have hι' : UniversalEnvelopingAlgebra.ι ℂ x ∈ degreeFiltration ℂ (LL n) 1 := by
              rw [degreeFiltration_one]; exact generator_mem_degreeOne ℂ (LL n) _
            have h := (realSymbol n).symbol_mul hι' hwF
            rw [add_comm 1 m] at h
            rw [word_cons, h, SymbolData.symbol_one_ι]
          rw [map_add, map_add,
            homogeneousComponent_eq_zero (m + 1) (q2 i) (by have := h21 i; omega),
            homogeneousComponent_eq_zero (m + 1) (q3 i) (by have := h31 i; omega), add_zero,
            add_zero,
            mul_comm, homogeneousComponent_mul_of_isHomogeneous _ (diagLin_isHomogeneous x),
            ite_eq_left (show 1 ≤ m + 1 by omega), show m + 1 - 1 = m by omega, h12 i, hsym, map_mul]
          simp only [diagLin]
          ring
        · intro a e T hT
          rw [word_cons, lam_ι_mul T hD hT, h13 a e T hT, h23 a e T hT, h33 a e T hT]
          have : evalVec a (fun i => diagLin x * q1 i + q2 i + q3 i) =
              eval a (diagLin x) • evalVec a q1 + evalVec a q2 + evalVec a q3 := by
            funext i; simp [evalVec]
          rw [this, map_add, map_add, map_smul, Submodule.coe_add, Submodule.coe_add,
            Submodule.coe_smul, Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    | zero =>
      intro v
      exact ⟨0, fun i => by simp, fun i => by simp, represents_zero v⟩
    | add u u' _ _ hu hu' =>
      intro v
      obtain ⟨q, hq1, hq2, hq3⟩ := hu v
      obtain ⟨q', hq1', hq2', hq3'⟩ := hu' v
      refine ⟨q + q', fun i => ?_, fun i => ?_, hq3.add hq3'⟩
      · exact (totalDegree_add _ _).trans (max_le (hq1 i) (hq1' i))
      · rw [Pi.add_apply, map_add, hq2 i, hq2' i, map_add, map_add, add_mul]
    | smul c u _ hu =>
      intro v
      obtain ⟨q, hq1, hq2, hq3⟩ := hu v
      refine ⟨fun i => C c * q i, fun i => ?_, fun i => ?_, hq3.smul c⟩
      · exact (totalDegree_mul _ _).trans (by simp [hq1 i])
      · rw [show (fun i => C c * q i) i = c • q i from (smul_eq_C_mul _ _).symm, map_smul,
          hq2 i, map_smul, map_smul, smul_eq_C_mul, smul_eq_C_mul]
        ring

/-! ## Uniqueness and the representative `Q` -/

/-- Representatives are unique: the principal series separate polynomial vectors. -/
theorem Represents.unique (hτ : Continuous τ) {u : UU n} {v : Fin d → ℂ}
    {q q' : Fin d → MvPolynomial (Fin n) ℂ} (h : Represents τ u v q)
    (h' : Represents τ u v q') : q = q' := by
  funext i
  refine MvPolynomial.funext fun a => ?_
  have key : evalVec a q - evalVec a q' = 0 := by
    refine eq_zero_of_signFunctional τ fun e φ hφ => ?_
    obtain ⟨T, hT, hT1⟩ := exists_frobenius_intertwiner hτ a e hφ
    have h1 := (h a e T hT).symm.trans (h' a e T hT)
    rw [map_sub, ← hT1, ← hT1, h1, sub_self]
  have := congrFun key i
  simpa [evalVec, sub_eq_zero] using this

open Classical in
variable (τ) in
/-- The polynomial representative `Q(u, v)` of `(u, v)` (zero if there is none). -/
def Q (u : UU n) (v : Fin d → ℂ) : Fin d → MvPolynomial (Fin n) ℂ :=
  if h : ∃ q, Represents τ u v q then Classical.choose h else 0

section QProps

variable {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
  (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hD in
theorem exists_represents' (u : UU n) (v : Fin d → ℂ) : ∃ q, Represents τ u v q := by
  obtain ⟨m, hm⟩ := exists_mem_degreeFiltration ℂ (LL n) u
  obtain ⟨q, -, -, hq⟩ := exists_represents hD m u (degreeFiltration_le_wordSpan ℂ (LL n) m hm) v
  exact ⟨q, hq⟩

include hD in
theorem Q_represents (u : UU n) (v : Fin d → ℂ) : Represents τ u v (Q τ u v) := by
  rw [Q, dite_eq_left (exists_represents' hD u v)]
  exact Classical.choose_spec (exists_represents' hD u v)

include hτ hD in
theorem Q_eq {u : UU n} {v : Fin d → ℂ} {q : Fin d → MvPolynomial (Fin n) ℂ}
    (h : Represents τ u v q) : Q τ u v = q :=
  (Q_represents hD u v).unique hτ h

include hτ hD in
theorem Q_add (u u' : UU n) (v : Fin d → ℂ) : Q τ (u + u') v = Q τ u v + Q τ u' v :=
  Q_eq hτ hD ((Q_represents hD u v).add (Q_represents hD u' v))

include hτ hD in
theorem Q_smul (c : ℂ) (u : UU n) (v : Fin d → ℂ) :
    Q τ (c • u) v = fun i => C c * Q τ u v i :=
  Q_eq hτ hD ((Q_represents hD u v).smul c)

include hτ hD in
theorem Q_add_right (u : UU n) (v v' : Fin d → ℂ) : Q τ u (v + v') = Q τ u v + Q τ u v' := by
  refine Q_eq hτ hD fun a e T hT => ?_
  have h1 := Q_represents hD u v a e T hT
  have h2 := Q_represents hD u v' a e T hT
  simp only [lam] at h1 h2 ⊢
  rw [map_add, map_add, Submodule.coe_add, Pi.add_apply, h1, h2, evalVec_add, map_add,
    Submodule.coe_add, Pi.add_apply]

include hτ hD in
theorem Q_smul_right (u : UU n) (c : ℂ) (v : Fin d → ℂ) :
    Q τ u (c • v) = fun i => C c * Q τ u v i := by
  refine Q_eq hτ hD fun a e T hT => ?_
  have h1 := Q_represents hD u v a e T hT
  simp only [lam] at h1 ⊢
  rw [map_smul, map_smul, Submodule.coe_smul, Pi.smul_apply, h1, evalVec_smul, map_smul,
    Submodule.coe_smul, Pi.smul_apply]

include hτ hD in
theorem Q_sum_right {ι : Type*} (s : Finset ι) (u : UU n) (v : ι → Fin d → ℂ) :
    Q τ u (∑ k ∈ s, v k) = ∑ k ∈ s, Q τ u (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := Q_smul_right hτ hD u 0 0
    simp only [zero_smul, map_zero, zero_mul] at h0
    simp only [Finset.sum_empty]
    rw [h0]
    rfl
  | insert k s hks ih => rw [Finset.sum_insert hks, Finset.sum_insert hks, Q_add_right hτ hD, ih]

include hτ hD in
/-- `Q` has degree at most `m` on `U_m`, with degree-`m` part `diagRes(σ_m(u)) v`. -/
theorem Q_degree {m : ℕ} {u : UU n} (hu : u ∈ degreeFiltration ℂ (LL n) m) (v : Fin d → ℂ) :
    (∀ i, (Q τ u v i).totalDegree ≤ m) ∧
      ∀ i, homogeneousComponent m (Q τ u v i) =
        diagRes n ((realSymbol n).symbol m u) * C (v i) := by
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_represents hD m u (degreeFiltration_le_wordSpan ℂ (LL n) m hu) v
  rw [Q_eq hτ hD hq3]
  exact ⟨hq1, hq2⟩

include hτ hD in
/-- `Q(u Y, v) = Q(u, D(Y) v)` for antisymmetric `Y`. -/
theorem Q_mul_skew (u : UU n) (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = -Y) (v : Fin d → ℂ) :
    Q τ (u * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y)) v = Q τ u (D Y *ᵥ v) := by
  refine Q_eq hτ hD fun a e T hT => ?_
  have h1 := Q_represents hD u (D Y *ᵥ v) a e T hT
  rw [← h1]
  simp only [lam]
  rw [map_mul, Module.End.mul_apply, psAct_ι,
    apply_skew_intertwiner (isRealGKModule_realStandardModule n (psList a e)) hD hT Y hY v]

end QProps

/-! ## Matrices over `U(𝔤)` acting on `K`-intertwiners -/

section Act

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (P : UU n →ₐ[ℂ] Module.End ℂ M)

/-- `(b · T)(e_i) = ∑ⱼ P(b i j) T(e_j)`. -/
def act (b : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    (Fin d → ℂ) →ₗ[ℂ] M where
  toFun x := ∑ i, x i • ∑ j, P (b i j) (T (Pi.single j 1))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem act_apply (b : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) (x : Fin d → ℂ) :
    act P b T x = ∑ i, x i • ∑ j, P (b i j) (T (Pi.single j 1)) :=
  rfl

theorem act_single (b : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) (i : Fin d)
    (c : ℂ) :
    act P b T (Pi.single i c) = c • ∑ j, P (b i j) (T (Pi.single j 1)) := by
  classical
  rw [act_apply, Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_eq_of_ne hi'])
    (by simp)]
  simp

theorem act_ext {b b' : Matrix (Fin d) (Fin d) (UU n)} {T T' : (Fin d → ℂ) →ₗ[ℂ] M}
    (h : ∀ i, ∑ j, P (b i j) (T (Pi.single j 1)) = ∑ j, P (b' i j) (T' (Pi.single j 1))) :
    act P b T = act P b' T' := by
  refine LinearMap.pi_ext fun i c => ?_
  rw [act_single, act_single, h i]

theorem act_mul (b b' : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    act P (b * b') T = act P b (act P b' T) := by
  refine act_ext P fun i => ?_
  simp only [act_single, one_smul, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_mul,
    Module.End.mul_apply]
  rw [Finset.sum_comm]

/-- Scalar matrices act through `τ`: `c · T = T ∘ cᵀ`. -/
theorem act_scalar (c : Matrix (Fin d) (Fin d) ℂ) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    act P (c.map (algebraMap ℂ (UU n))) T = T ∘ₗ Matrix.toLin' cᵀ := by
  classical
  refine LinearMap.pi_ext fun i x => ?_
  rw [act_single, LinearMap.comp_apply, Matrix.toLin'_apply]
  have hv : cᵀ *ᵥ Pi.single i x = x • ∑ j, c i j • (Pi.single j 1 : Fin d → ℂ) := by
    funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply, mul_comm]
  rw [hv, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, AlgHom.commutes, Module.algebraMap_end_apply, map_smul]

/-- A linear map intertwining `P` with `P ∘ φ` moves through the action. -/
theorem comp_act (f : M →ₗ[ℂ] M) (φ : UU n →ₐ[ℂ] UU n) (hf : ∀ u, f ∘ₗ P u = P (φ u) ∘ₗ f)
    (b : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    f ∘ₗ act P b T = act P (b.map φ) (f ∘ₗ T) := by
  refine LinearMap.pi_ext fun i x => ?_
  rw [LinearMap.comp_apply, act_single, act_single, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, ← LinearMap.comp_apply f, hf, LinearMap.comp_apply, LinearMap.comp_apply]

end Act

variable (τ) in
/-- The `K`-invariant matrices over `U(𝔤)`: `τ(k)ᵀ b = Ad(k)(b) τ(k)ᵀ` for all `k ∈ O(n)`. -/
def InB (b : Matrix (Fin d) (Fin d) (UU n)) : Prop :=
  ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
    (τ k)ᵀ.map (algebraMap ℂ (UU n)) * b =
      b.map (envMap (conjLie (orthUnit k))) * (τ k)ᵀ.map (algebraMap ℂ (UU n))

/-- `K`-invariant matrices preserve `K`-intertwiners. -/
theorem act_mem {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M} (P : UU n →ₐ[ℂ] Module.End ℂ M)
    (hρP : ∀ k u, ρ k * P u = P (envMap (conjLie (orthUnit k)) u) * ρ k)
    {b : Matrix (Fin d) (Fin d) (UU n)} (hb : InB τ b) {T : (Fin d → ℂ) →ₗ[ℂ] M}
    (hT : T ∈ gkIntertwiners ρ d τ) : act P b T ∈ gkIntertwiners ρ d τ := by
  intro k x
  have h1 : act P b T ∘ₗ Matrix.toLin' (τ k) = act P ((τ k)ᵀ.map (algebraMap ℂ (UU n)) * b) T := by
    rw [act_mul, act_scalar, Matrix.transpose_transpose]
  have hTk : ρ k ∘ₗ T = T ∘ₗ Matrix.toLin' (τ k) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, hT k y]
  have h2 : ρ k ∘ₗ act P b T =
      act P (b.map (envMap (conjLie (orthUnit k))) * (τ k)ᵀ.map (algebraMap ℂ (UU n))) T := by
    rw [comp_act P (ρ k) _ (fun u => hρP k u), hTk, act_mul, act_scalar,
      Matrix.transpose_transpose]
  have := congrArg (fun f => f x) (h1.trans ((congrArg (fun c => act P c T) (hb k)).trans h2.symm))
  simpa [Matrix.toLin'_apply] using this

/-! ## The matrix `ĉ(b)` -/

variable (τ) in
/-- `ĉ(b)`: the matrix of polynomials whose `i`-th column is `∑ⱼ Q(b i j, e_j)`. -/
def chat (b : Matrix (Fin d) (Fin d) (UU n)) : Matrix (Fin d) (Fin d) (MvPolynomial (Fin n) ℂ) :=
  Matrix.of fun m i => ∑ j, Q τ (b i j) (Pi.single j 1) m

section Chat

variable {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
  (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hD in
/-- The principal series: `((b · T) x)(1) = (T (ĉ(b)(a) x))(1)`. -/
theorem eval_one_act_psAct {a : Fin n → ℂ} {e : Fin n → Fin 2}
    {T : (Fin d → ℂ) →ₗ[ℂ] PS a e} (hT : T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ)
    (b : Matrix (Fin d) (Fin d) (UU n)) (x : Fin d → ℂ) :
    ((act (psAct a e) b T x : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 =
      ((T ((chat τ b).map (eval a) *ᵥ x) : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
  suffices h : kFiniteEval (realStandardModule n (psList a e)) 1 ∘ₗ act (psAct a e) b T =
      kFiniteEval (realStandardModule n (psList a e)) 1 ∘ₗ T ∘ₗ
        Matrix.toLin' ((chat τ b).map (eval a)) by
    have := LinearMap.congr_fun h x
    simpa [Matrix.toLin'_apply, kFiniteEval_apply] using this
  refine LinearMap.pi_ext fun i c => ?_
  have hvec : (chat τ b).map (eval a) *ᵥ Pi.single i c =
      c • ∑ j, evalVec a (Q τ (b i j) (Pi.single j 1)) := by
    funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, chat, evalVec, Finset.sum_apply,
      mul_comm]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
    hvec, act_single]
  simp only [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Q_represents hD (b i j) (Pi.single j 1) a e T hT
  simpa [lam, kFiniteEval_apply] using this

include hτ hD in
/-- `ĉ` is an antihomomorphism on `K`-invariant matrices: `ĉ(b b') = ĉ(b') ĉ(b)`. -/
theorem chat_mul (b : Matrix (Fin d) (Fin d) (UU n)) {b' : Matrix (Fin d) (Fin d) (UU n)}
    (hb' : InB τ b') : chat τ (b * b') = chat τ b' * chat τ b := by
  refine Matrix.ext fun m i => ?_
  refine MvPolynomial.funext fun a => ?_
  have key : ∀ x : Fin d → ℂ, (chat τ (b * b')).map (eval a) *ᵥ x =
      (chat τ b').map (eval a) *ᵥ ((chat τ b).map (eval a) *ᵥ x) := by
    intro x
    rw [← sub_eq_zero]
    refine eq_zero_of_signFunctional τ fun e φ hφ => ?_
    obtain ⟨T, hT, hT1⟩ := exists_frobenius_intertwiner hτ a e hφ
    have hρP : ∀ k u, realStandardRep n (psList a e) k * psAct a e u =
        psAct a e (envMap (conjLie (orthUnit k)) u) * realStandardRep n (psList a e) k :=
      fun k u => rho_mul_envelopingAction
        (isRealGKModule_realStandardModule n (psList a e)).2.2.2 k u
    have hT' := act_mem (psAct a e) hρP hb' hT
    rw [map_sub, ← hT1, ← hT1, ← eval_one_act_psAct hD hT, act_mul,
      eval_one_act_psAct hD hT', eval_one_act_psAct hD hT, sub_self]
  have := congrFun (key (Pi.single i 1)) m
  simpa [Matrix.mul_apply, map_sum, Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Chat

/-! ## Central elements act on the principal series through a polynomial -/

/-- The subspace `J_a ⊆ U(𝔤)` spanned by `x u - ℓ_a(x) u` for `x = c ⊗ X`, `X` upper
triangular and `ℓ_a(c ⊗ X) = c ∑ⱼ aⱼ Xⱼⱼ`. -/
def Jideal (a : Fin n → ℂ) : Submodule ℂ (UU n) :=
  Submodule.span ℂ {w | ∃ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) (u : UU n), X.IsUpperTriangular ∧
    w = UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ X) * u - (c * ∑ j, a j * (X j j : ℂ)) • u}

/-- Left multiplication of `U(𝔤)` on itself, as a representation of `𝔤`. -/
def lmulRep (n : ℕ) : LL n →ₗ⁅ℂ⁆ Module.End ℂ (UU n) :=
  (Algebra.lmul ℂ (UU n)).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)

theorem envelopingAction_lmulRep (u w : UU n) : envelopingAction (lmulRep n) u w = u * w := by
  have h : envelopingAction (lmulRep n) = Algebra.lmul ℂ (UU n) := by
    ext x
    simp [envelopingAction, lmulRep]
  rw [h]
  rfl

/-- Every central element is congruent to a scalar modulo `J_a` (Harish-Chandra's argument of
`JacquetCenter.exists_comp_envelopingAction_eq_smul`, applied to left multiplication on
`U(𝔤)` and the functionals vanishing on `J_a`). -/
theorem exists_sub_mem_Jideal (a : Fin n → ℂ) {z : UU n}
    (hz : z ∈ Subalgebra.center ℂ (UU n)) : ∃ c : ℂ, z - algebraMap ℂ (UU n) c ∈ Jideal a := by
  -- every functional vanishing on `J_a` sees `z` as a scalar
  have key : ∀ ℓ : UU n →ₗ[ℂ] ℂ, Jideal a ≤ LinearMap.ker ℓ → ∃ c : ℂ, ℓ z = c * ℓ 1 := by
    intro ℓ hℓ
    have hscal : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℝ), X.IsUpperTriangular →
        ℓ ∘ₗ lmulRep n (c ⊗ₜ X) = (c * ∑ j, a j * (X j j : ℂ)) • ℓ := by
      intro c X hX
      refine LinearMap.ext fun u => ?_
      have hmem : UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ X) * u -
          (c * ∑ j, a j * (X j j : ℂ)) • u ∈ Jideal a :=
        Submodule.subset_span ⟨c, X, u, hX, rfl⟩
      have h0 := hℓ hmem
      rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h0
      simpa [lmulRep] using h0
    have hdecTop : JacquetCenter.decSubmodule (lmulRep n) ℓ RealPrincipalSeriesInfChar.lowering =
        ⊤ := by
      rw [eq_top_iff]
      rintro x -
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => exact Submodule.add_mem _ hx hy
      | tmul c X =>
        rw [Matrix.matrix_eq_sum_single X, TensorProduct.tmul_sum]
        refine Submodule.sum_mem _ fun p _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Submodule.sum_mem _ fun q _ => ?_
        rcases lt_or_ge q p with hqp | hpq
        · exact JacquetCenter.subset_decSubmodule _ _ _ ⟨p, q, c, _, hqp, rfl⟩
        · refine JacquetCenter.scalarSubmodule_le_decSubmodule _ _ _ ⟨_, hscal c _ ?_⟩
          intro i j hji
          rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            exact absurd hpq (not_le.2 hji)
          · rfl
    have hdec : ∀ x : LL n, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ RealPrincipalSeriesInfChar.lowering,
        ℓ ∘ₗ lmulRep n x = c • ℓ + ℓ ∘ₗ lmulRep n y := fun x =>
      (JacquetCenter.mem_decSubmodule _ _ _).1 (by rw [hdecTop]; trivial)
    have hH := hscal 1 (Matrix.diagonal fun p => -((p : ℕ) : ℝ)) (Matrix.blockTriangular_diagonal _)
    obtain ⟨c, hc⟩ := JacquetCenter.exists_comp_envelopingAction_eq_smul
      RealPrincipalSeriesInfChar.weightH _ hH RealPrincipalSeriesInfChar.lie_weightH_lowering hdec hz
    refine ⟨c, ?_⟩
    have := LinearMap.congr_fun hc 1
    simpa [envelopingAction_lmulRep] using this
  refine by_contra fun hcon' => ?_
  have hcon : ∀ c : ℂ, z - algebraMap ℂ (UU n) c ∉ Jideal a := fun c hc => hcon' ⟨c, hc⟩
  set J := Jideal a
  have h1 : J.mkQ z ∉ Submodule.span ℂ {J.mkQ 1} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply hcon c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
      Algebra.algebraMap_eq_smul_one, Submodule.Quotient.mk_smul]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hc
    rw [hc, sub_self]
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_notMem h1
  obtain ⟨c, hc⟩ := key (f ∘ₗ J.mkQ) fun w hw => by simp [(Submodule.Quotient.mk_eq_zero J).2 hw]
  have h1' : f (J.mkQ 1) = 0 := hle (Submodule.mem_span_singleton_self _)
  apply hf
  rw [Submodule.mkQ_apply] at h1' ⊢
  simpa [h1'] using hc

/-- `J_a` acts by zero on evaluation at `1` of the principal series of `chars a e`. -/
theorem eval_one_psAct_Jideal {a : Fin n → ℂ} {e : Fin n → Fin 2} {w : UU n}
    (hw : w ∈ Jideal a) (G : PS a e) :
    ((psAct a e w G : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, X, u, hX, rfl⟩ := hw
    set F := psAct a e u G
    have hF : (F : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n (posChar a e) :=
      realStandardModule_le_principalSeries n (psList a e) F.2.1
    have hcX : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [map_sub, map_mul, map_smul, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, psAct_ι, hcX, map_smul, LinearMap.smul_apply, Submodule.coe_sub,
      Submodule.coe_smul, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
      realStandardLie_one_tmul_apply_coe, rightDerivative_upper_apply_one hF hX]
    simp only [smul_eq_mul]
    ring
  | zero => simp
  | add w w' _ _ h h' => simp [h, h']
  | smul c w _ h => simp [h]

/-- A central element acts on evaluation at `1` of every principal series of `chars a e` by one
scalar, independent of the signs `e`. -/
theorem exists_eval_one_central (a : Fin n → ℂ) {z : UU n}
    (hz : z ∈ Subalgebra.center ℂ (UU n)) :
    ∃ c : ℂ, ∀ (e : Fin n → Fin 2) (G : PS a e),
      ((psAct a e z G : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 =
        c * (G : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
  obtain ⟨c, hc⟩ := exists_sub_mem_Jideal a hz
  refine ⟨c, fun e G => ?_⟩
  have h := eval_one_psAct_Jideal (e := e) hc G
  rw [map_sub, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  rw [h, AlgHom.commutes, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul]

section Central

variable {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
  (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hτ hD in
/-- **Central elements are scalar polynomials.** For central `z` there is a polynomial `ξ` with
`Q(z, v) = ξ v`. -/
theorem exists_Q_central {z : UU n} (hz : z ∈ Subalgebra.center ℂ (UU n)) :
    ∃ ξ : MvPolynomial (Fin n) ℂ, ∀ (v : Fin d → ℂ) (i : Fin d), Q τ z v i = ξ * C (v i) := by
  choose c hc using fun a : Fin n → ℂ => exists_eval_one_central a hz
  -- pointwise, `Q(z, v)(a) = c(a) v`
  have hpt : ∀ (a : Fin n → ℂ) (v : Fin d → ℂ), evalVec a (Q τ z v) = c a • v := by
    intro a v
    rw [← sub_eq_zero]
    refine eq_zero_of_signFunctional τ fun e φ hφ => ?_
    obtain ⟨T, hT, hT1⟩ := exists_frobenius_intertwiner hτ a e hφ
    have h1 := Q_represents hD z v a e T hT
    simp only [lam] at h1
    rw [map_sub, map_smul, ← hT1, ← hT1, ← h1, hc a e, smul_eq_mul, sub_self]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, fun v i => i.elim0⟩
  · set i0 : Fin d := ⟨0, hd⟩
    refine ⟨Q τ z (Pi.single i0 1) i0, fun v i => ?_⟩
    refine MvPolynomial.funext fun a => ?_
    have h1 := congrFun (hpt a v) i
    have h2 := congrFun (hpt a (Pi.single i0 1)) i0
    simp only [evalVec, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at h1 h2
    rw [map_mul, eval_C, h1, h2]

end Central

end RealSubquotient

end Langlands.Archimedean
