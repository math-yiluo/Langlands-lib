import Langlands.Representation.Archimedean.ComplexBlockJacquet
import Langlands.Representation.Archimedean.GKModuleDensity
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.ComplexJacquetDual

/-!
# The dual step along `P_{a,k+1}`: orthogonality passes to `GL_a(ℂ)`

Let `U` be a nonzero `(𝔤, K)`-stable space of `U(a+k+1)`-finite functions of the principal series
of `χ⁻¹` on `GL_{a+k+1}(ℂ)` and `h` a `U(a+k+1)`-finite function of the principal series of `χ`
orthogonal to `U`, where the last `k+1` exponents of `χ` are tied. If the principal series of the
tied block (with the inverse characters) is irreducible, then for every `U(k+1)`-finite `φ` of it
and every `u ∈ U`, `∫_{U(a)} u(diag(κ₁, 1)) h'(κ₁) dκ₁ = 0` with
`h' = ComplexBlockJacquet.blockPair φ h`. The proof uses Jacobson density
(`GKModuleDensity`) on the tied block to replace `u(diag(κ₁, κ₂))` by `u(diag(κ₁, 1)) φ(κ₂)`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexBlockDual

open ComplexBlockParabolic ComplexBlockChart ComplexBlockLimit ComplexBlockJacquet
  ComplexPartialJacquet ComplexJacquetLimit ComplexGramFormula ComplexPrincipalSeriesExtension
  ComplexDuality Langlands.GeneralLinear

/-! ## Admissibility of the complex principal series -/

section Admissible

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ} (V : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
  (hVK : ∀ k ∈ unitaryCompact ℂ n, ∀ f ∈ V,
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f ∈ V)

/-- The functional `x ↦ (T x)(1)` of a `K`-intertwiner `T` into the `K`-finite functions of `V`. -/
def valueAtOne (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners (kFiniteRep V hVK) d τ →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] ℂ) where
  toFun T :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℂ => ℂ) 1).comp
      ((kFiniteFunctions V (unitaryCompact ℂ n)).subtype.comp (T : (Fin d → ℂ) →ₗ[ℂ] _))
  map_add' S T := by
    ext x
    rfl
  map_smul' c T := by
    ext x
    rfl

theorem valueAtOne_apply (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ) :
    valueAtOne V hVK d τ T x =
      ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℂ n)) x :
        Langlands.GeneralLinear n ℂ → ℂ) 1 :=
  rfl

theorem intertwiner_apply_unitary (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℂ n)) x :
        Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
      valueAtOne V hVK d τ T (τ k *ᵥ x) := by
  rw [valueAtOne_apply, T.2 k x, kFiniteRep_apply_coe]
  change _ = ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℂ n)) x :
    Langlands.GeneralLinear n ℂ → ℂ) (1 * Unitary.toUnits k)
  rw [one_mul]

variable {V}

include hVK in
theorem valueAtOne_injective (hVχ : V ≤ principalSeries ℂ n χ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Function.Injective (valueAtOne V hVK d τ) := by
  intro S T hST
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  refine eq_of_eqOn_unitary
    (hVχ (((S : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℂ n)) x).2.1))
    (hVχ (((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℂ n)) x).2.1)) ?_
  intro k hk
  have hk' : (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℂ) : Langlands.GeneralLinear n ℂ) = k :=
    Units.ext rfl
  rw [← hk', intertwiner_apply_unitary, intertwiner_apply_unitary, hST]

include hVK in
/-- The `U(n)`-finite functions of a right-translation-stable subspace of a complex principal
series form an admissible representation of `U(n)`. -/
theorem isAdmissibleGKModule_kFiniteRep (hVχ : V ≤ principalSeries ℂ n χ) :
    IsAdmissibleGKModule (kFiniteRep V hVK) := by
  intro d τ _
  exact Module.Finite.of_injective _ (valueAtOne_injective hVK hVχ d τ)

end Admissible

/-! ## Composition with affine group embeddings -/

section Embed

variable {m N : ℕ}

/-- **Smoothness.** If `ι : GL_m(ℂ) → GL_N(ℂ)` is given on matrices by an affine map
`Y ↦ L Y + C`, then `x ↦ u(c ι(x))` is smooth for smooth `u`. -/
theorem contMDiff_comp_affine {u : Langlands.GeneralLinear N ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ N) 𝓘(ℝ, ℂ) ∞ u)
    (ι : Langlands.GeneralLinear m ℂ → Langlands.GeneralLinear N ℂ)
    (L : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (C : Matrix (Fin N) (Fin N) ℂ)
    (hι : ∀ g, ((ι g : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      L (g : Matrix (Fin m) (Fin m) ℂ) + C)
    (c : Langlands.GeneralLinear N ℂ) :
    ContMDiff (matrixModel ℂ m) 𝓘(ℝ, ℂ) ∞ (fun x => u (c * ι x)) := by
  refine contMDiff_of_contDiffOn
    (ψ := fun Y => unitsExtension u ((c : Matrix (Fin N) (Fin N) ℂ) * (L Y + C))) ?_ fun g => ?_
  · have hA : ContDiff ℝ ∞ fun Y : Matrix (Fin m) (Fin m) ℂ =>
        (c : Matrix (Fin N) (Fin N) ℂ) * (L Y + C) :=
      contDiff_const.mul (L.contDiff.add contDiff_const)
    refine (contDiffOn_unitsExtension hu).comp hA.contDiffOn fun Y hY => ?_
    have hY' : IsUnit Y := hY
    have h1 : L Y + C = ((ι hY'.unit : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
      rw [hι, IsUnit.unit_spec]
    change IsUnit ((c : Matrix (Fin N) (Fin N) ℂ) * (L Y + C))
    rw [h1, ← Units.val_mul]
    exact Units.isUnit _
  · rw [← hι, ← Units.val_mul, unitsExtension_val]

/-- **Derivatives.** If moreover `L(g Y) = ι(g) L(Y)`, then the right derivative of
`x ↦ u(c ι(x))` along `Y` is the right derivative of `u` along `L Y` at `c ι(x)`. -/
theorem rightDerivative_comp_affine {u : Langlands.GeneralLinear N ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ N) 𝓘(ℝ, ℂ) ∞ u)
    (ι : Langlands.GeneralLinear m ℂ → Langlands.GeneralLinear N ℂ)
    (L : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (C : Matrix (Fin N) (Fin N) ℂ)
    (hι : ∀ g, ((ι g : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      L (g : Matrix (Fin m) (Fin m) ℂ) + C)
    (hL : ∀ (g : Langlands.GeneralLinear m ℂ) (Y : Matrix (Fin m) (Fin m) ℂ),
      L ((g : Matrix (Fin m) (Fin m) ℂ) * Y) =
        ((ι g : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) * L Y)
    (c : Langlands.GeneralLinear N ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (g : Langlands.GeneralLinear m ℂ) :
    rightDerivative (matrixModel ℂ m) Y (fun x => u (c * ι x)) g =
      rightDerivative (matrixModel ℂ N) (L Y) u (c * ι g) := by
  have hsm := contMDiff_comp_affine hu ι L C hι c
  rw [rightDerivative_eq_fderiv hsm, rightDerivative_eq_fderiv hu]
  set A : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin N) (Fin N) ℂ :=
    fun Y => (c : Matrix (Fin N) (Fin N) ℂ) * (L Y + C) with hAdef
  have hev : unitsExtension (fun x => u (c * ι x)) =ᶠ[𝓝 (g : Matrix (Fin m) (Fin m) ℂ)]
      unitsExtension u ∘ A := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with y hy
    have hy' : IsUnit y := hy
    have h1 : y = ((hy'.unit : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
      (IsUnit.unit_spec hy').symm
    rw [h1, unitsExtension_val, Function.comp_apply, hAdef]
    simp only
    rw [← hι, ← Units.val_mul, unitsExtension_val]
  rw [hev.fderiv_eq]
  have hAg : A (g : Matrix (Fin m) (Fin m) ℂ) =
      ((c * ι g : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hAdef, Units.val_mul, hι]
  have hAd : HasFDerivAt A ((c : Matrix (Fin N) (Fin N) ℂ) • L)
      (g : Matrix (Fin m) (Fin m) ℂ) :=
    (L.hasFDerivAt.add_const C).const_mul (c : Matrix (Fin N) (Fin N) ℂ)
  have hE : DifferentiableAt ℝ (unitsExtension u) (A (g : Matrix (Fin m) (Fin m) ℂ)) := by
    rw [hAg]
    exact differentiableAt_unitsExtension hu (Units.isUnit _)
  rw [fderiv_comp _ hE hAd.differentiableAt, hAd.fderiv, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, hAg, hL, smul_eq_mul, ← mul_assoc, ← Units.val_mul]

end Embed

/-! ## The block embeddings `g₁ ↦ diag(g₁, 1)` and `g₂ ↦ diag(1, g₂)` -/

section Block

variable {a b : ℕ}

theorem blockDiag_add (A A' : Matrix (Fin a) (Fin a) ℂ) (D D' : Matrix (Fin b) (Fin b) ℂ) :
    ComplexBlockParabolic.blockDiag (A + A') (D + D') =
      ComplexBlockParabolic.blockDiag A D + ComplexBlockParabolic.blockDiag A' D' := by
  rw [ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockDiag,
    ComplexBlockParabolic.blockDiag, ← add_zero (0 : Matrix (Fin a) (Fin b) ℂ),
    ← add_zero (0 : Matrix (Fin b) (Fin a) ℂ), ← Matrix.fromBlocks_add]
  simp only [add_zero]
  ext i j
  simp [Matrix.reindex_apply]

theorem blockDiag_smul (r : ℝ) (A : Matrix (Fin a) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    ComplexBlockParabolic.blockDiag (r • A) (r • D) = r • ComplexBlockParabolic.blockDiag A D := by
  rw [ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockDiag]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;> simp

theorem blockDiag_mul (A A' : Matrix (Fin a) (Fin a) ℂ) (D D' : Matrix (Fin b) (Fin b) ℂ) :
    ComplexBlockParabolic.blockDiag A D * ComplexBlockParabolic.blockDiag A' D' =
      ComplexBlockParabolic.blockDiag (A * A') (D * D') := by
  rw [ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockDiag,
    ComplexBlockParabolic.blockDiag, reindex_mul_reindex, Matrix.fromBlocks_multiply]
  simp

/-- `A ↦ diag(A, 0)`. -/
def leftLin : Matrix (Fin a) (Fin a) ℂ →L[ℝ] Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ComplexBlockParabolic.blockDiag A (0 : Matrix (Fin b) (Fin b) ℂ)
      map_add' := fun A A' => by
        rw [← blockDiag_add, add_zero]
      map_smul' := fun r A => by
        rw [RingHom.id_apply, ← blockDiag_smul, smul_zero] }

/-- `D ↦ diag(0, D)`. -/
def rightLin : Matrix (Fin b) (Fin b) ℂ →L[ℝ] Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => ComplexBlockParabolic.blockDiag (0 : Matrix (Fin a) (Fin a) ℂ) D
      map_add' := fun D D' => by
        rw [← blockDiag_add, add_zero]
      map_smul' := fun r D => by
        rw [RingHom.id_apply, ← blockDiag_smul, smul_zero] }

theorem leftLin_apply (A : Matrix (Fin a) (Fin a) ℂ) :
    leftLin (b := b) A = ComplexBlockParabolic.blockDiag A 0 := rfl

theorem rightLin_apply (D : Matrix (Fin b) (Fin b) ℂ) :
    rightLin (a := a) D = ComplexBlockParabolic.blockDiag 0 D := rfl

theorem blockDiagGL_left_val (g : Langlands.GeneralLinear a ℂ) :
    ((blockDiagGL g (1 : Langlands.GeneralLinear b ℂ) : Langlands.GeneralLinear (a + b) ℂ) :
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ) =
      leftLin (g : Matrix (Fin a) (Fin a) ℂ) + ComplexBlockParabolic.blockDiag 0 1 := by
  rw [blockDiagGL_val, leftLin_apply, ← blockDiag_add, add_zero, zero_add, Units.val_one]

theorem blockDiagGL_right_val (g : Langlands.GeneralLinear b ℂ) :
    ((blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g : Langlands.GeneralLinear (a + b) ℂ) :
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ) =
      rightLin (g : Matrix (Fin b) (Fin b) ℂ) + ComplexBlockParabolic.blockDiag 1 0 := by
  rw [blockDiagGL_val, rightLin_apply, ← blockDiag_add, add_zero, zero_add, Units.val_one]

theorem leftLin_mul (g : Langlands.GeneralLinear a ℂ) (Y : Matrix (Fin a) (Fin a) ℂ) :
    leftLin (b := b) ((g : Matrix (Fin a) (Fin a) ℂ) * Y) =
      ((blockDiagGL g (1 : Langlands.GeneralLinear b ℂ) : Langlands.GeneralLinear (a + b) ℂ) :
        Matrix (Fin (a + b)) (Fin (a + b)) ℂ) * leftLin Y := by
  rw [blockDiagGL_val, leftLin_apply, leftLin_apply, blockDiag_mul, Units.val_one, mul_zero]

theorem rightLin_mul (g : Langlands.GeneralLinear b ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    rightLin (a := a) ((g : Matrix (Fin b) (Fin b) ℂ) * Y) =
      ((blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g : Langlands.GeneralLinear (a + b) ℂ) :
        Matrix (Fin (a + b)) (Fin (a + b)) ℂ) * rightLin Y := by
  rw [blockDiagGL_val, rightLin_apply, rightLin_apply, blockDiag_mul, Units.val_one, mul_zero]

theorem blockDiagGL_one_one :
    blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear b ℂ) = 1 := by
  apply Units.ext
  rw [blockDiagGL_val, Units.val_one, Units.val_one, Units.val_one,
    ComplexBlockParabolic.blockDiag, Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

theorem blockDiagGL_eq_mul (g₁ : Langlands.GeneralLinear a ℂ) (g₂ : Langlands.GeneralLinear b ℂ) :
    blockDiagGL g₁ g₂ = blockDiagGL g₁ 1 * blockDiagGL 1 g₂ := by
  rw [← blockDiagGL_mul, mul_one, one_mul]

theorem blockDiagGL_diagonalUnits_right (z : Fin b → ℂˣ) :
    blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (Iwasawa.diagonalUnits z) =
      Iwasawa.diagonalUnits (Fin.addCases (fun _ => 1) z) := by
  apply Units.ext
  rw [blockDiagGL_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Units.val_one,
    ComplexBlockParabolic.blockDiag]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Fin.castAdd_inj, Fin.natAdd_inj]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem blockDiagGL_mem_upperUnipotent_right (v : upperUnipotent b ℂ) :
    blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (v : Langlands.GeneralLinear b ℂ) ∈
      upperUnipotent (a + b) ℂ := by
  have hval := blockDiagGL_val (1 : Langlands.GeneralLinear a ℂ) (v : Langlands.GeneralLinear b ℂ)
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change j < i at hij
    change ((blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (v : Langlands.GeneralLinear b ℂ) :
      Langlands.GeneralLinear (a + b) ℂ) : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) i j = 0
    rw [hval, ComplexBlockParabolic.blockDiag]
    revert hij
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
      refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;> intro hij
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁, Units.val_one]
      rw [Matrix.one_apply_ne]
      intro h
      subst h
      exact lt_irrefl _ hij
    · exfalso
      rw [Fin.lt_def] at hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hij
      omega
    · simp
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₂]
      exact v.2.1 (show q' < q by
        rw [Fin.lt_def] at hij ⊢
        simp only [Fin.val_natAdd] at hij
        omega)
  · change ((blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (v : Langlands.GeneralLinear b ℂ) :
      Langlands.GeneralLinear (a + b) ℂ) : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) i i = 1
    rw [hval, ComplexBlockParabolic.blockDiag]
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₂]
      exact v.2.2 q

end Block

/-! ## Restriction to `GL_a(ℂ)` and slices along `GL_{k+1}(ℂ)` -/

section Restrict

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- `u ↦ (g₁ ↦ u(diag(g₁, 1)))`. -/
def restrictBlock :
    (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear a ℂ → ℂ) where
  toFun u g := u (blockDiagGL g (1 : Langlands.GeneralLinear (k + 1) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictBlock_apply (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (g : Langlands.GeneralLinear a ℂ) :
    restrictBlock (k := k) u g = u (blockDiagGL g (1 : Langlands.GeneralLinear (k + 1) ℂ)) := rfl

/-- `u ↦ (g₂ ↦ u(diag(κ₁, g₂)))`. -/
def sliceFun (κ₁ : Langlands.GeneralLinear a ℂ) :
    (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) →ₗ[ℂ]
      (Langlands.GeneralLinear (k + 1) ℂ → ℂ) where
  toFun u g := u (blockDiagGL κ₁ g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sliceFun_apply (κ₁ : Langlands.GeneralLinear a ℂ)
    (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (g : Langlands.GeneralLinear (k + 1) ℂ) :
    sliceFun κ₁ u g = u (blockDiagGL κ₁ g) := rfl

/-- The characters `(χ_{a+l}(z))⁻¹ (|z|²)^{-a/2}` of the dual principal series of the tied block. -/
def blockDualChar (a : ℕ) (χ : ℕ → ℂˣ → ℂ) (l : ℕ) (z : ℂˣ) : ℂ :=
  (χ (a + l) z)⁻¹ * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-((a : ℂ) / 2))

theorem contMDiff_restrictBlock {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ (a + (k + 1))) 𝓘(ℝ, ℂ) ∞ u) :
    ContMDiff (matrixModel ℂ a) 𝓘(ℝ, ℂ) ∞ (restrictBlock (k := k) u) := by
  have h := contMDiff_comp_affine hu (fun g => blockDiagGL g (1 : Langlands.GeneralLinear (k + 1) ℂ))
    leftLin (ComplexBlockParabolic.blockDiag 0 1) blockDiagGL_left_val 1
  have heq : (fun x => u (1 * blockDiagGL x (1 : Langlands.GeneralLinear (k + 1) ℂ))) =
      restrictBlock (k := k) u := funext fun x => by rw [one_mul]; rfl
  rwa [heq] at h

theorem rightDerivative_restrictBlock {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ (a + (k + 1))) 𝓘(ℝ, ℂ) ∞ u) (Y : Matrix (Fin a) (Fin a) ℂ) :
    rightDerivative (matrixModel ℂ a) Y (restrictBlock (k := k) u) =
      restrictBlock (rightDerivative (matrixModel ℂ (a + (k + 1)))
        (ComplexBlockParabolic.blockDiag Y 0) u) := by
  funext g
  have h := rightDerivative_comp_affine hu
    (fun g => blockDiagGL g (1 : Langlands.GeneralLinear (k + 1) ℂ))
    leftLin (ComplexBlockParabolic.blockDiag 0 1) blockDiagGL_left_val leftLin_mul 1 Y g
  have heq : (fun x => u (1 * blockDiagGL x (1 : Langlands.GeneralLinear (k + 1) ℂ))) =
      restrictBlock (k := k) u := funext fun x => by rw [one_mul]; rfl
  rw [heq, one_mul] at h
  exact h

theorem sliceFun_eq (κ₁ : Langlands.GeneralLinear a ℂ)
    (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) :
    sliceFun κ₁ u = fun x => u (blockDiagGL κ₁ (1 : Langlands.GeneralLinear (k + 1) ℂ) *
      blockDiagGL (1 : Langlands.GeneralLinear a ℂ) x) :=
  funext fun x => by rw [sliceFun_apply, ← blockDiagGL_eq_mul]

theorem contMDiff_sliceFun {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ (a + (k + 1))) 𝓘(ℝ, ℂ) ∞ u) (κ₁ : Langlands.GeneralLinear a ℂ) :
    ContMDiff (matrixModel ℂ (k + 1)) 𝓘(ℝ, ℂ) ∞ (sliceFun κ₁ u) := by
  rw [sliceFun_eq]
  exact contMDiff_comp_affine hu (fun g => blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g)
    rightLin (ComplexBlockParabolic.blockDiag 1 0) blockDiagGL_right_val _

theorem rightDerivative_sliceFun {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ContMDiff (matrixModel ℂ (a + (k + 1))) 𝓘(ℝ, ℂ) ∞ u) (κ₁ : Langlands.GeneralLinear a ℂ)
    (Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    rightDerivative (matrixModel ℂ (k + 1)) Y (sliceFun κ₁ u) =
      sliceFun κ₁ (rightDerivative (matrixModel ℂ (a + (k + 1)))
        (ComplexBlockParabolic.blockDiag 0 Y) u) := by
  funext g
  rw [sliceFun_eq κ₁ u]
  rw [rightDerivative_comp_affine hu (fun g => blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g)
    rightLin (ComplexBlockParabolic.blockDiag 1 0) blockDiagGL_right_val rightLin_mul _ Y g,
    sliceFun_apply, blockDiagGL_eq_mul κ₁ g]
  rfl

theorem rightTranslation_restrictBlock (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (κ : Langlands.GeneralLinear a ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear a ℂ) κ (restrictBlock (k := k) u) =
      restrictBlock (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (blockDiagGL κ (1 : Langlands.GeneralLinear (k + 1) ℂ)) u) := by
  funext g
  change u (blockDiagGL (g * κ) 1) = u (blockDiagGL g 1 * blockDiagGL κ 1)
  rw [← blockDiagGL_mul, mul_one]

theorem rightTranslation_sliceFun (κ₁ : Langlands.GeneralLinear a ℂ)
    (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (k + 1) ℂ) κ₂ (sliceFun κ₁ u) =
      sliceFun κ₁ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) κ₂) u) := by
  funext g
  change u (blockDiagGL κ₁ (g * κ₂)) = u (blockDiagGL κ₁ g * blockDiagGL 1 κ₂)
  rw [← blockDiagGL_mul, mul_one]

theorem sliceFun_eq_sliceFun_one (κ₁ : Langlands.GeneralLinear a ℂ)
    (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) :
    sliceFun κ₁ u = sliceFun 1 (Whittaker.rightTranslation ℂ
      (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (blockDiagGL κ₁ (1 : Langlands.GeneralLinear (k + 1) ℂ)) u) := by
  funext g
  change u (blockDiagGL κ₁ g) = u (blockDiagGL 1 g * blockDiagGL κ₁ 1)
  rw [← blockDiagGL_mul, one_mul, mul_one]

theorem principalSeriesCharacter_addCases_dual (hχ : IsPhasePower χ e) (z : Fin a → ℂˣ) :
    principalSeriesCharacter ℂ (a + (k + 1)) (dualChar χ) (Fin.addCases z (fun _ => 1)) =
      principalSeriesCharacter ℂ a (dualChar (blockShiftChar k χ)) z := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [show (∏ x : Fin (k + 1), dualChar χ (a + (x : ℕ)) 1) = 1 from
    Finset.prod_eq_one fun j _ => by simp [dualChar, hχ.one], mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [dualChar, blockShiftChar, Complex.finrank_real_complex]
  have hx : ((‖(z i : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (z i).ne_zero)
  rw [mul_inv, ← Complex.cpow_neg, neg_neg, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2
  push_cast
  ring

theorem principalSeriesCharacter_addCases_right_dual (hχ : IsPhasePower χ e)
    (z : Fin (k + 1) → ℂˣ) :
    principalSeriesCharacter ℂ (a + (k + 1)) (dualChar χ) (Fin.addCases (fun _ => 1) z) =
      principalSeriesCharacter ℂ (k + 1) (blockDualChar a χ) z := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [show (∏ x : Fin a, dualChar χ (x : ℕ) 1) = 1 from
    Finset.prod_eq_one fun j _ => by simp [dualChar, hχ.one], one_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [dualChar, blockDualChar, Complex.finrank_real_complex]
  have hx : ((‖(z i : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (z i).ne_zero)
  rw [mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2
  push_cast
  ring

theorem restrictBlock_mem (hχ : IsPhasePower χ e) {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1)))) :
    restrictBlock (k := k) u ∈ kFiniteFunctions (principalSeries ℂ a
      (dualChar (blockShiftChar k χ))) (unitaryCompact ℂ a) := by
  refine ⟨⟨contMDiff_restrictBlock hu.1.1, fun z v g => ?_⟩, ?_⟩
  · rw [restrictBlock_apply, restrictBlock_apply]
    have hsplit : blockDiagGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℂ) *
        (v : Langlands.GeneralLinear a ℂ) * g) (1 : Langlands.GeneralLinear (k + 1) ℂ) =
        (Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        ((⟨blockDiagGL (v : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear (k + 1) ℂ),
          blockDiagGL_mem_upperUnipotent v⟩ : upperUnipotent (a + (k + 1)) ℂ) :
            Langlands.GeneralLinear (a + (k + 1)) ℂ) * blockDiagGL g 1 := by
      rw [← blockDiagGL_diagonalUnits]
      change _ = blockDiagGL (Iwasawa.diagonalUnits z) 1 *
        blockDiagGL (v : Langlands.GeneralLinear a ℂ) 1 * blockDiagGL g 1
      rw [← blockDiagGL_mul, ← blockDiagGL_mul, one_mul, one_mul]
    rw [hsplit, hu.1.2, principalSeriesCharacter_addCases_dual hχ]
  · refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
    have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ
        (a + (k + 1)) => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
          (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)) :=
      (mem_kFiniteVectors_iff _ _ _).mp hu.2
    have hle : Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ a =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear a ℂ)
          (κ : Langlands.GeneralLinear a ℂ) (restrictBlock (k := k) u)) ≤
        (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
            (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)).map restrictBlock := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨κ, rfl⟩
      refine ⟨_, Submodule.subset_span ⟨⟨blockDiagGL (κ : Langlands.GeneralLinear a ℂ) 1,
        blockDiagGL_mem_unitaryCompact κ.2 (unitaryCompact ℂ (k + 1)).one_mem⟩, rfl⟩, ?_⟩
      exact (rightTranslation_restrictBlock u κ).symm
    exact Submodule.finiteDimensional_of_le hle

theorem sliceFun_mem (hχ : IsPhasePower χ e) {χT : ℕ → ℂˣ → ℂ}
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ, χT l z = blockDualChar a χ l z)
    {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1)))) (κ₁ : Langlands.GeneralLinear a ℂ) :
    sliceFun κ₁ u ∈ kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)) := by
  refine ⟨⟨contMDiff_sliceFun hu.1.1 κ₁, fun z v g => ?_⟩, ?_⟩
  · rw [sliceFun_apply, sliceFun_apply]
    have hsplit : blockDiagGL κ₁ ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
        (v : Langlands.GeneralLinear (k + 1) ℂ) * g) =
        (Iwasawa.diagonalUnits (Fin.addCases (fun _ => 1) z) :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        ((⟨blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (v : Langlands.GeneralLinear (k + 1) ℂ),
          blockDiagGL_mem_upperUnipotent_right v⟩ : upperUnipotent (a + (k + 1)) ℂ) :
            Langlands.GeneralLinear (a + (k + 1)) ℂ) * blockDiagGL κ₁ g := by
      rw [← blockDiagGL_diagonalUnits_right]
      change _ = blockDiagGL 1 (Iwasawa.diagonalUnits z) *
        blockDiagGL 1 (v : Langlands.GeneralLinear (k + 1) ℂ) * blockDiagGL κ₁ g
      rw [← blockDiagGL_mul, ← blockDiagGL_mul, one_mul, one_mul]
    rw [hsplit, hu.1.2, principalSeriesCharacter_addCases_right_dual hχ]
    congr 1
    rw [principalSeriesCharacter, principalSeriesCharacter]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hT i i.isLt]
  · refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
    have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ
        (a + (k + 1)) => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
          (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)) :=
      (mem_kFiniteVectors_iff _ _ _).mp hu.2
    have hle : Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (k + 1) =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (k + 1) ℂ)
          (κ : Langlands.GeneralLinear (k + 1) ℂ) (sliceFun κ₁ u)) ≤
        (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
            (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)).map (sliceFun κ₁) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨κ, rfl⟩
      refine ⟨_, Submodule.subset_span ⟨⟨blockDiagGL (1 : Langlands.GeneralLinear a ℂ)
        (κ : Langlands.GeneralLinear (k + 1) ℂ),
        blockDiagGL_mem_unitaryCompact (unitaryCompact ℂ a).one_mem κ.2⟩, rfl⟩, ?_⟩
      exact (rightTranslation_sliceFun κ₁ u κ).symm
    exact Submodule.finiteDimensional_of_le hle

end Restrict

/-! ## Density on the tied block -/

section Density

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} {χT : ℕ → ℂˣ → ℂ}

/-- The hypotheses of `GKModuleDensity` for an irreducible complex principal series. -/
theorem hyp_principalSeries {n : ℕ} {ψ : ℕ → ℂˣ → ℂ}
    (hirr : IsIrreducibleGKModule (principalSeriesRep ℂ n ψ) (principalSeriesLie ℂ n ψ)) :
    GKModuleDensity.Hyp (principalSeriesRep ℂ n ψ) (principalSeriesLie ℂ n ψ) where
  irreducible := hirr
  admissible := isAdmissibleGKModule_kFiniteRep (V := principalSeries ℂ n ψ)
    (fun κ _ _ hf => rightTranslation_mem_principalSeries ψ hf κ) le_rfl
  finite v := ⟨FiniteVectors.orbitSpan (principalSeriesRep ℂ n ψ) v,
    FiniteVectors.self_mem_orbitSpan _ v,
    kFiniteRep_isFiniteVector (principalSeries ℂ n ψ)
      (fun k _ _ hf => rightTranslation_mem_principalSeries ψ hf k) v,
    fun g _ hw => (FiniteVectors.orbitSubrepresentation _ v).apply_mem_toSubmodule g hw⟩
  continuous v ℓ := kFiniteRep_continuous (principalSeries ℂ n ψ) (fun _ hf => hf.1)
    (fun k _ _ hf => rightTranslation_mem_principalSeries ψ hf k) v ℓ

variable (hχ : IsPhasePower χ e)
  (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ, χT l z = blockDualChar a χ l z)
  {U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)}
  (hU : U ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (unitaryCompact ℂ (a + (k + 1))))

/-- The slice `g₂ ↦ u(diag(κ₁, g₂))` of `u ∈ U`, in the principal series of the tied block. -/
def sliceV (κ₁ : Langlands.GeneralLinear a ℂ) (u : U) :
    kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)) :=
  ⟨sliceFun κ₁ (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ), sliceFun_mem hχ hT (hU u.2) κ₁⟩

theorem sliceV_coe (κ₁ : Langlands.GeneralLinear a ℂ) (u : U) :
    ((sliceV hχ hT hU κ₁ u : kFiniteFunctions (principalSeries ℂ (k + 1) χT)
      (unitaryCompact ℂ (k + 1))) : Langlands.GeneralLinear (k + 1) ℂ → ℂ) =
      sliceFun κ₁ (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) := rfl

theorem sliceV_add (κ₁ : Langlands.GeneralLinear a ℂ) (u v : U) :
    sliceV hχ hT hU κ₁ (u + v) = sliceV hχ hT hU κ₁ u + sliceV hχ hT hU κ₁ v :=
  Subtype.ext (map_add (sliceFun κ₁) _ _)

theorem sliceV_smul (κ₁ : Langlands.GeneralLinear a ℂ) (c : ℂ) (u : U) :
    sliceV hχ hT hU κ₁ (c • u) = c • sliceV hχ hT hU κ₁ u :=
  Subtype.ext (map_smul (sliceFun κ₁) _ _)

include hχ hT hU in
/-- **Lifting the algebra.** Every element `A` of the free algebra on `U(k+1)` and
`ℂ ⊗ 𝔤𝔩_{k+1}(ℂ)`, acting on the tied block, is realized on all slices of an element of `U` at
once by another element of `U`: right translations by `diag(1, κ₂)` and right derivatives along
`diag(0, Y)` act on slices as `κ₂` and `Y` do. -/
theorem exists_sliceV_eq
    (hUK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u ∈ U)
    (hUD : ∀ (X : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (a + (k + 1))) X u ∈ U)
    (A : FreeAlgebra ℂ (Matrix.unitaryGroup (Fin (k + 1)) ℂ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))) :
    ∀ u : U, ∃ u' : U, ∀ κ₁ : Langlands.GeneralLinear a ℂ,
      sliceV hχ hT hU κ₁ u' = FreeAlgebra.lift ℂ (GKModuleDensity.gens
        (principalSeriesRep ℂ (k + 1) χT) (principalSeriesLie ℂ (k + 1) χT)) A
          (sliceV hχ hT hU κ₁ u) := by
  induction A using FreeAlgebra.induction with
  | grade0 r =>
    intro u
    refine ⟨r • u, fun κ₁ => ?_⟩
    rw [AlgHom.commutes, Module.algebraMap_end_apply, sliceV_smul]
  | grade1 x =>
    rw [FreeAlgebra.lift_ι_apply]
    cases x with
    | inl κ₂ =>
      intro u
      have hκ : blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (Unitary.toUnits κ₂) ∈
          unitaryCompact ℂ (a + (k + 1)) :=
        blockDiagGL_mem_unitaryCompact (unitaryCompact ℂ a).one_mem κ₂.2
      refine ⟨⟨_, hUK _ hκ _ u.2⟩, fun κ₁ => ?_⟩
      apply Subtype.ext
      simp only [GKModuleDensity.gens, Sum.elim_inl]
      rw [sliceV_coe, principalSeriesRep_apply_coe, sliceV_coe, rightTranslation_sliceFun]
    | inr X =>
      simp only [GKModuleDensity.gens, Sum.elim_inr]
      induction X using TensorProduct.inductionOn with
      | tmul z Y =>
        intro u
        refine ⟨⟨z • rightDerivative (matrixModel ℂ (a + (k + 1)))
          (ComplexBlockParabolic.blockDiag 0 Y) (u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ),
          U.smul_mem z (hUD _ _ u.2)⟩, fun κ₁ => ?_⟩
        have htmul : (z ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
            z • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        apply Subtype.ext
        rw [htmul, map_smul, LinearMap.smul_apply, Submodule.coe_smul,
          principalSeriesLie_one_tmul_apply_coe, sliceV_coe, sliceV_coe,
          rightDerivative_sliceFun (hU u.2).1.1, map_smul]
      | add X₁ X₂ h₁ h₂ =>
        intro u
        obtain ⟨u₁, hu₁⟩ := h₁ u
        obtain ⟨u₂, hu₂⟩ := h₂ u
        refine ⟨u₁ + u₂, fun κ₁ => ?_⟩
        rw [map_add, LinearMap.add_apply, sliceV_add, hu₁, hu₂]
  | mul A B hA hB =>
    intro u
    obtain ⟨uB, huB⟩ := hB u
    obtain ⟨uAB, huAB⟩ := hA uB
    refine ⟨uAB, fun κ₁ => ?_⟩
    rw [map_mul, Module.End.mul_apply, ← huB, huAB]
  | add A B hA hB =>
    intro u
    obtain ⟨uA, huA⟩ := hA u
    obtain ⟨uB, huB⟩ := hB u
    refine ⟨uA + uB, fun κ₁ => ?_⟩
    rw [map_add, LinearMap.add_apply, sliceV_add, huA, huB]

end Density

/-! ## The dual step -/

section Step

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} {χT : ℕ → ℂˣ → ℂ}

/-- **The dual step.** Assume the block statements, `IsBlockDominant e a k`, and that the
principal series of the characters `χT = blockDualChar a χ` (on `l < k+1`) of `GL_{k+1}(ℂ)` is
irreducible. Let `U` be a `(𝔤, K)`-stable space of `U(a+k+1)`-finite functions of the principal
series of `χ⁻¹`, and `h` a `U(a+k+1)`-finite function of the principal series of `χ` with
`∫_{U(a+k+1)} u h = 0` for `u ∈ U`. Then for every `U(k+1)`-finite `φ` of the principal series of
`χT` and every `u ∈ U`, `∫_{U(a)} u(diag(κ₁, 1)) blockPair φ h (κ₁) dκ₁ = 0`. -/
theorem integral_restrictBlock_mul_blockPair_eq_zero
    (hT1 : ComplexBlockChartIntegrableStatement) (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) (he : IsBlockDominant e a k)
    (hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ, χT l z = blockDualChar a χ l z)
    (hirr : IsIrreducibleGKModule (principalSeriesRep ℂ (k + 1) χT)
      (principalSeriesLie ℂ (k + 1) χT))
    {U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1))))
    (hUK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u ∈ U)
    (hUD : ∀ (X : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (a + (k + 1))) X u ∈ U)
    {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))))
    (horth : ∀ u ∈ U, ∫ κ, u (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * h κ
      ∂unitaryHaar (a + (k + 1)) = 0)
    (φ : kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)))
    {u : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ} (hu : u ∈ U) :
    ∫ κ₁ : unitaryCompact ℂ a, restrictBlock (k := k) u κ₁ *
      blockPair (φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ) h κ₁ ∂unitaryHaar a = 0 := by
  have hF3 := ComplexJacquetDual.integral_mul_eq_zero_of_orthogonal hχ hU hUK hUD
    hh.1.1.continuous horth
  set u0 : U := ⟨u, hu⟩ with hu0
  -- a finite-dimensional space containing all slices of `u`
  set W : Submodule ℂ (Langlands.GeneralLinear (k + 1) ℂ → ℂ) :=
    (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)).map (sliceFun 1) with hWdef
  have hWfin : FiniteDimensional ℂ W := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ
        (a + (k + 1)) => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
          (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) u)) :=
      (mem_kFiniteVectors_iff _ _ _).mp (hU hu).2
    infer_instance
  set S : Submodule ℂ (kFiniteFunctions (principalSeries ℂ (k + 1) χT)
    (unitaryCompact ℂ (k + 1))) :=
    W.comap (kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))).subtype
    with hSdef
  have hSfin : FiniteDimensional ℂ S := by
    refine Module.Finite.of_injective (LinearMap.codRestrict W
      ((kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))).subtype ∘ₗ
        S.subtype) fun x => x.2) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W =>
      (z : Langlands.GeneralLinear (k + 1) ℂ → ℂ)) hxy))
  have hslice : ∀ κ₁ : unitaryCompact ℂ a, sliceV hχ hT hU (κ₁ : Langlands.GeneralLinear a ℂ) u0 ∈ S := by
    intro κ₁
    change sliceFun (κ₁ : Langlands.GeneralLinear a ℂ) u ∈ W
    rw [sliceFun_eq_sliceFun_one]
    refine ⟨_, Submodule.subset_span ⟨⟨blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) 1,
      blockDiagGL_mem_unitaryCompact κ₁.2 (unitaryCompact ℂ (k + 1)).one_mem⟩, rfl⟩, rfl⟩
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).mpr hSfin
  -- the rank-one target map `v ↦ v(1) φ`
  set f : Module.End ℂ (kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1))) :=
    (kFiniteEval (principalSeries ℂ (k + 1) χT) 1).smulRight φ with hfdef
  obtain ⟨A, hA⟩ := GKModuleDensity.exists_freeAlgebra_eq (hyp_principalSeries hirr) s f
  have hAS : ∀ v ∈ S, FreeAlgebra.lift ℂ (GKModuleDensity.gens (principalSeriesRep ℂ (k + 1) χT)
      (principalSeriesLie ℂ (k + 1) χT)) A v = f v := by
    intro v hv
    rw [← hs] at hv
    exact LinearMap.eqOn_span (fun w hw => hA w hw) hv
  obtain ⟨u', hu'⟩ := exists_sliceV_eq hχ hT hU hUK hUD A u0
  have hpt : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1)),
      (u' : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
        (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) =
      u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) 1) *
        (φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ) κ₂ := by
    intro κ₁ κ₂
    have h1 := congrArg (fun v : kFiniteFunctions (principalSeries ℂ (k + 1) χT)
      (unitaryCompact ℂ (k + 1)) => (v : Langlands.GeneralLinear (k + 1) ℂ → ℂ)
        (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))
      ((hu' (κ₁ : Langlands.GeneralLinear a ℂ)).trans (hAS _ (hslice κ₁)))
    simp only [sliceV_coe, sliceFun_apply, hfdef, LinearMap.smulRight_apply, kFiniteEval_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact h1
  have hlim := integral_mul_blockStep_eq_zero hT1 hT3 hχ he.tie he.ord he.gap (hU u'.2).1 hh.1
    (hF3 _ u'.2)
  refine Eq.trans ?_ hlim
  refine integral_congr_ae (ae_of_all _ fun κ₁ => ?_)
  simp only [restrictBlock_apply, blockPair, blockStep]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [hpt]
  ring

/-- The restriction `U' = {g₁ ↦ u(diag(g₁, 1))}` of a nonzero `(𝔤, K)`-stable `U` is a nonzero
`(𝔤_a, U(a))`-stable space of `U(a)`-finite functions of the principal series of
`(blockShiftChar k χ)⁻¹`. -/
theorem map_restrictBlock (hχ : IsPhasePower χ e)
    {U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℂ (a + (k + 1))))
    (hUK : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u ∈ U)
    (hUD : ∀ (X : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (a + (k + 1))) X u ∈ U) (hU0 : U ≠ ⊥) :
    U.map (restrictBlock (k := k)) ≤ kFiniteFunctions (principalSeries ℂ a
        (dualChar (blockShiftChar k χ))) (unitaryCompact ℂ a) ∧
      (∀ κ ∈ unitaryCompact ℂ a, ∀ u ∈ U.map (restrictBlock (k := k)),
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear a ℂ) κ u ∈
          U.map (restrictBlock (k := k))) ∧
      (∀ (Y : Matrix (Fin a) (Fin a) ℂ), ∀ u ∈ U.map (restrictBlock (k := k)),
        rightDerivative (matrixModel ℂ a) Y u ∈ U.map (restrictBlock (k := k))) ∧
      U.map (restrictBlock (k := k)) ≠ ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact restrictBlock_mem hχ (hU hu)
  · rintro κ hκ _ ⟨u, hu, rfl⟩
    rw [rightTranslation_restrictBlock]
    exact ⟨_, hUK _ (blockDiagGL_mem_unitaryCompact hκ (unitaryCompact ℂ (k + 1)).one_mem) u hu,
      rfl⟩
  · rintro Y _ ⟨u, hu, rfl⟩
    rw [rightDerivative_restrictBlock (hU hu).1.1]
    exact ⟨_, hUD _ u hu, rfl⟩
  · obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨κ, hκ, hκ0⟩ : ∃ κ ∈ unitaryCompact ℂ (a + (k + 1)), u κ ≠ 0 := by
      by_contra hcon
      exact hu0 (eq_zero_of_mem_principalSeries_of_eqOn (hU huU).1
        fun k hk => by_contra fun h => hcon ⟨k, hk, h⟩)
    intro hbot
    have hmem : restrictBlock (k := k) (Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u) ∈ U.map (restrictBlock (k := k)) :=
      ⟨_, hUK κ hκ u huU, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have := congrFun hmem 1
    change u (blockDiagGL 1 1 * κ) = 0 at this
    rw [blockDiagGL_one_one, one_mul] at this
    exact hκ0 this

end Step

end ComplexBlockDual

open ComplexDuality ComplexBlockParabolic ComplexBlockChart in
/-- **The dual step along `P_{a,k+1}`** (assuming `ComplexBlockChartIntegrableStatement` and
`ComplexBlockParabolicIntegrationStatement`). Let `χ` be phase-power characters with exponents `e`
such that `Re e_{l+1} ≤ Re e_l` for `l < a`, `Re e_a < Re e_{a−1}` (if `a ≥ 1`) and
`Re e_a = ⋯ = Re e_{a+k}`, and let `χT` be characters with
`χT_l(z) = χ_{a+l}(z)⁻¹ (|z|²)^{-a/2}` for `l ≤ k` whose `U(k+1)`-finite principal series of
`GL_{k+1}(ℂ)` is irreducible. Let `U` be a subspace of the `U(a+k+1)`-finite functions of the
principal series of the inverse characters of `χ` on `GL_{a+k+1}(ℂ)`, stable under right
translation by `U(a+k+1)` and under right derivatives, and `h` a `U(a+k+1)`-finite function of the
principal series of `χ` with `∫_{U(a+k+1)} u h = 0` for all `u ∈ U`. Then for every
`U(k+1)`-finite `φ` of the principal series of `χT` and every `u ∈ U`,
`∫_{U(a)} u(diag(κ₁, 1)) · (∫_{U(k+1)} φ(κ₂) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂) dκ₁ = 0`. -/
def ComplexBlockDualStatement : Prop :=
  ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
  ∀ (a k : ℕ) (χ χT : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re) →
    (∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re) →
    (∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re) →
    (∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ,
      χT l z = (χ (a + l) z)⁻¹ * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-((a : ℂ) / 2))) →
    IsIrreducibleGKModule (principalSeriesRep ℂ (k + 1) χT) (principalSeriesLie ℂ (k + 1) χT) →
    ∀ U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ),
    U ≤ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) (fun l z => (χ l z)⁻¹))
      (unitaryCompact ℂ (a + (k + 1))) →
    (∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) κ u ∈ U) →
    (∀ (X : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (a + (k + 1))) X u ∈ U) →
    ∀ h ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))),
    (∀ u ∈ U, ∫ κ, u (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * h κ
      ∂unitaryHaar (a + (k + 1)) = 0) →
    ∀ φ ∈ kFiniteFunctions (principalSeries ℂ (k + 1) χT) (unitaryCompact ℂ (k + 1)),
    ∀ u ∈ U,
      ∫ κ₁ : unitaryCompact ℂ a,
        u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear (k + 1) ℂ)) *
          ComplexBlockJacquet.blockPair φ h κ₁ ∂unitaryHaar a = 0

theorem complexBlockDual : ComplexBlockDualStatement := by
  intro hT1 hT3 a k χ χT e heq hone hphase hord hgap htie hT hirr U hU hUK hUD h hh horth φ hφ u hu
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  have he : ComplexBlockJacquet.IsBlockDominant e a k := ⟨htie, hord, hgap⟩
  exact ComplexBlockDual.integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he hT hirr hU hUK
    hUD hh horth ⟨φ, hφ⟩ hu

end Langlands.Archimedean
