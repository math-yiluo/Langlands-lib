import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Algebra.ReducedNormFiniteChart
import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.GroupScheme.Examples.HermitianMatrixSplitting

/-! # Components of the relative reduced norm in matrix charts -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple.UnitaryPoints

open Langlands.GroupScheme Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]

section Quotient

variable (F E B) (R : Type*) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]

/-- For an `E`-algebra `R`, the natural `R`-algebra map `R ⊗[F] B → R ⊗[E] B`,
`r ⊗ b ↦ r ⊗ b`. -/
def tensorQuotient : R ⊗[F] B →ₐ[R] R ⊗[E] B :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.restrictScalars F)
    (fun r b => by
      change (r ⊗ₜ[E] (1 : B)) * ((1 : R) ⊗ₜ[E] b) = ((1 : R) ⊗ₜ[E] b) * (r ⊗ₜ[E] (1 : B))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, one_mul, mul_one])

@[simp] theorem tensorQuotient_tmul (r : R) (b : B) :
    tensorQuotient F E B R (r ⊗ₜ[F] b) = r ⊗ₜ[E] b := by
  change (r ⊗ₜ[E] (1 : B)) * ((1 : R) ⊗ₜ[E] b) = r ⊗ₜ[E] b
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem tensorQuotient_surjective : Function.Surjective (tensorQuotient F E B R) := by
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul r b => exact ⟨r ⊗ₜ[F] b, tensorQuotient_tmul F E B R r b⟩
  | add w w' hw hw' =>
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨y', rfl⟩ := hw'
    exact ⟨y + y', map_add _ _ _⟩

end Quotient

section Involution

variable (τ : FirstKindInvolution F B)

/-- The involution `τ_R = id ⊗ τ` on the units of `R ⊗[F] B`. -/
def involutionUnits (R : Type u) [CommRing R] [Algebra F R] (x : (R ⊗[F] B)ˣ) :
    (R ⊗[F] B)ˣ where
  val := τ.baseChange R x
  inv := τ.baseChange R ↑x⁻¹
  val_inv := by rw [← FirstKindInvolution.map_mul, Units.inv_mul, FirstKindInvolution.map_one]
  inv_val := by rw [← FirstKindInvolution.map_mul, Units.mul_inv, FirstKindInvolution.map_one]

@[simp] theorem involutionUnits_val (R : Type u) [CommRing R] [Algebra F R]
    (x : (R ⊗[F] B)ˣ) : (involutionUnits τ R x : R ⊗[F] B) = τ.baseChange R x := rfl

/-- On a unitary point the involution is the inverse. -/
theorem involutionUnits_eq_inv {R : Type u} [CommRing R] [Algebra F R] {x : (R ⊗[F] B)ˣ}
    (hx : x ∈ unitaryPoints τ R) : involutionUnits τ R x = x⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (Units.ext hx)

end Involution

variable [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

/-- For an `E`-algebra `R`, the component of the relative reduced norm along
`e ⊗ r ↦ e r` is the reduced norm over `E` of the image in `R ⊗[E] B`. -/
theorem tensorProj_relativeNorm_eq_reducedNorm [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E] (R : Type u) [CommRing R] [Algebra F R] [Algebra E R]
    [IsScalarTower F E R] (x : (R ⊗[F] B)ˣ) :
    HermitianMatrix.tensorProj F E (IsScalarTower.toAlgHom F E R)
        (relativeNorm F E B R x : E ⊗[F] R) =
      reducedNorm E B R (tensorQuotient F E B R (x : R ⊗[F] B)) := by
  let π : E ⊗[F] R →ₐ[E] R :=
    Algebra.TensorProduct.lift (Algebra.ofId E R) (AlgHom.id F R) (fun _ _ => Commute.all _ _)
  have hπ (w : E ⊗[F] R) :
      π w = HermitianMatrix.tensorProj F E (IsScalarTower.toAlgHom F E R) w := by
    induction w using TensorProduct.inductionOn with
    | tmul e r => simp [π]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  have hq (y : R ⊗[F] B) : Algebra.TensorProduct.map π (AlgHom.id E B) (tensorEquiv F E B R y) =
      tensorQuotient F E B R y := by
    induction y using TensorProduct.inductionOn with
    | tmul r b =>
      have h0 : tensorEquiv F E B R (r ⊗ₜ[F] b) = ((1 : E) ⊗ₜ[F] r) ⊗ₜ[E] b := rfl
      have h1 : π (1 ⊗ₜ[F] r) = r := by simp [π]
      rw [h0, Algebra.TensorProduct.map_tmul, h1, AlgHom.id_apply, tensorQuotient_tmul]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  rw [← hπ, relativeNorm_val, ← reducedNorm_naturality E B π, hq]

/-- In a surjective `R`-algebra matrix chart of `R ⊗[F] B` which sends `e ∈ E` to the
scalar `e`, the reduced norm of the image in `R ⊗[E] B` is the determinant. -/
theorem reducedNorm_tensorQuotient_eq_det (R : Type u) [Field R] [Algebra F R] [Algebra E R]
    [IsScalarTower F E R] {m : Type*} [Fintype m] [DecidableEq m]
    (hm : Module.finrank E B = Fintype.card m * Fintype.card m)
    (C : R ⊗[F] B →ₐ[R] Matrix m m R) (hC : Function.Surjective C)
    (hCE : ∀ e : E, C (1 ⊗ₜ[F] algebraMap E B e) =
      algebraMap R (Matrix m m R) (algebraMap E R e))
    (y : R ⊗[F] B) :
    reducedNorm E B R (tensorQuotient F E B R y) = (C y).det := by
  let g : B →ₐ[E] Matrix m m R :=
    { toFun := fun b => C (1 ⊗ₜ[F] b)
      map_one' := by rw [← Algebra.TensorProduct.one_def, map_one]
      map_mul' := fun a b => by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
      map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add]
      commutes' := fun e => by
        rw [hCE]
        rfl }
  let e₂ : R ⊗[E] B →ₐ[R] Matrix m m R :=
    Algebra.TensorProduct.lift (Algebra.ofId R (Matrix m m R)) g
      (fun r b => Algebra.commute_algebraMap_left r (g b))
  have hq (y : R ⊗[F] B) : e₂ (tensorQuotient F E B R y) = C y := by
    induction y using TensorProduct.inductionOn with
    | tmul r b =>
      rw [tensorQuotient_tmul]
      change algebraMap R (Matrix m m R) r * C (1 ⊗ₜ[F] b) = _
      rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  have hsurj : Function.Surjective e₂ := by
    intro M
    obtain ⟨y, rfl⟩ := hC M
    exact ⟨tensorQuotient F E B R y, hq y⟩
  have hdim : Module.finrank R (R ⊗[E] B) = Module.finrank R (Matrix m m R) := by
    rw [Module.finrank_baseChange, hm, Module.finrank_matrix, Module.finrank_self, mul_one]
  have hinj : Function.Injective e₂ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e₂.toLinearMap)).mpr
      hsurj
  let e : R ⊗[E] B ≃ₐ[R] Matrix m m R := AlgEquiv.ofBijective e₂ ⟨hinj, hsurj⟩
  rw [reducedNorm_eq_chart_det_fintype E B e]
  exact congrArg Matrix.det (hq y)

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- A component of the relative reduced norm is the determinant in any surjective matrix
chart of `R ⊗[F] B` which is `R`-linear and sends `e ∈ E` to the scalar `φ e`. -/
theorem tensorProj_relativeNorm_eq_det {R : Type u} [Field R] [Algebra F R] (φ : E →ₐ[F] R)
    {m : Type*} [Fintype m] [DecidableEq m]
    (hm : Module.finrank E B = Fintype.card m * Fintype.card m)
    (C : R ⊗[F] B →ₐ[R] Matrix m m R) (hC : Function.Surjective C)
    (hCE : ∀ e : E, C (1 ⊗ₜ[F] algebraMap E B e) = algebraMap R (Matrix m m R) (φ e))
    (x : (R ⊗[F] B)ˣ) :
    HermitianMatrix.tensorProj F E φ (relativeNorm F E B R x : E ⊗[F] R) =
      (C (x : R ⊗[F] B)).det := by
  let : Algebra E R := φ.toRingHom.toAlgebra
  have : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  have hφ : IsScalarTower.toAlgHom F E R = φ := by
    ext e
    rfl
  have h := tensorProj_relativeNorm_eq_reducedNorm (F := F) (E := E) (B := B) R x
  rw [hφ] at h
  rw [h]
  exact reducedNorm_tensorQuotient_eq_det R hm C hC hCE _

section Conjugation

variable (τ : FirstKindInvolution F B)

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- Over an algebraically closed field, every `F`-algebra map `φ : E → Ω` gives a surjective
matrix chart of `Ω ⊗[F] B` sending `e ∈ E` to the scalar `φ e`. -/
theorem exists_surjective_chart (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    (φ : E →ₐ[F] Ω) :
    ∃ C : Ω ⊗[F] B →ₐ[Ω] Matrix (Fin (reducedDegree E B)) (Fin (reducedDegree E B)) Ω,
      Function.Surjective C ∧ ∀ e : E, C (1 ⊗ₜ[F] algebraMap E B e) =
        algebraMap Ω (Matrix (Fin (reducedDegree E B)) (Fin (reducedDegree E B)) Ω) (φ e) := by
  let : Algebra E Ω := φ.toRingHom.toAlgebra
  have : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  obtain ⟨e₁⟩ := exists_matrix_chart_reducedDegree E B Ω
  refine ⟨e₁.toAlgHom.comp (tensorQuotient F E B Ω),
    e₁.surjective.comp (tensorQuotient_surjective F E B Ω), fun e => ?_⟩
  change e₁ (tensorQuotient F E B Ω (1 ⊗ₜ[F] algebraMap E B e)) = _
  rw [tensorQuotient_tmul, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]
  change e₁ (algebraMap Ω (Ω ⊗[E] B) (φ e)) = _
  exact e₁.commutes (φ e)

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
theorem algebraMap_matrix_transpose {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    [DecidableEq m] (r : R) : (algebraMap R (Matrix m m R) r).transpose =
      algebraMap R (Matrix m m R) r := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]

variable (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))
include hτ

/-- Over an algebraically closed field `Ω`, the component of the relative reduced norm
along `φ ∘ conj` is the component along `φ` of the relative reduced norm of `τ_Ω(y)`. -/
theorem tensorProj_conjugation_relativeNorm (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra F Ω] (φ : E →ₐ[F] Ω) (y : (Ω ⊗[F] B)ˣ) :
    HermitianMatrix.tensorProj F E (φ.comp (conjugation F E).toAlgHom)
        (relativeNorm F E B Ω y : E ⊗[F] Ω) =
      HermitianMatrix.tensorProj F E φ
        (relativeNorm F E B Ω (involutionUnits τ Ω y) : E ⊗[F] Ω) := by
  obtain ⟨C, hC, hCE⟩ := exists_surjective_chart (B := B) Ω φ
  have hm : Module.finrank E B =
      Fintype.card (Fin (reducedDegree E B)) * Fintype.card (Fin (reducedDegree E B)) := by
    rw [Fintype.card_fin]
    exact finrank_eq_reducedDegree_mul_self E B
  let C' : Ω ⊗[F] B →ₐ[Ω] Matrix (Fin (reducedDegree E B)) (Fin (reducedDegree E B)) Ω :=
    { toFun := fun w => (C (τ.baseChange Ω w)).transpose
      map_one' := by rw [FirstKindInvolution.map_one, map_one, Matrix.transpose_one]
      map_mul' := fun a b => by
        rw [FirstKindInvolution.map_mul, map_mul, Matrix.transpose_mul]
      map_zero' := by rw [FirstKindInvolution.map_zero, map_zero, Matrix.transpose_zero]
      map_add' := fun a b => by
        rw [FirstKindInvolution.map_add, map_add, Matrix.transpose_add]
      commutes' := fun r => by
        rw [FirstKindInvolution.map_algebraMap, C.commutes, algebraMap_matrix_transpose] }
  have hC' : Function.Surjective C' := by
    intro M
    obtain ⟨w, hw⟩ := hC M.transpose
    refine ⟨τ.baseChange Ω w, ?_⟩
    change (C (τ.baseChange Ω (τ.baseChange Ω w))).transpose = M
    rw [FirstKindInvolution.apply_apply, hw, Matrix.transpose_transpose]
  have hCE' (e : E) : C' (1 ⊗ₜ[F] algebraMap E B e) =
      algebraMap Ω _ ((φ.comp (conjugation F E).toAlgHom) e) := by
    change (C (τ.baseChange Ω (1 ⊗ₜ[F] algebraMap E B e))).transpose = _
    rw [FirstKindInvolution.baseChange_tmul, hτ, hCE, algebraMap_matrix_transpose]
    rfl
  rw [tensorProj_relativeNorm_eq_det _ hm C' hC' hCE', tensorProj_relativeNorm_eq_det _ hm C hC hCE]
  change (C (τ.baseChange Ω (y : Ω ⊗[F] B))).transpose.det = _
  rw [Matrix.det_transpose]
  rfl

/-- If `z ⊗ 1` is the relative reduced norm of a unitary point over some field, then
`z z̄ = 1`. -/
theorem mul_conjugation_eq_one {K : Type u} [Field K] [Algebra F K] (z : E)
    (x : (K ⊗[F] B)ˣ) (hx : x ∈ unitaryPoints τ K)
    (hz : (relativeNorm F E B K x : E ⊗[F] K) = z ⊗ₜ[F] (1 : K)) :
    z * conjugation F E z = 1 := by
  let Ω := AlgebraicClosure K
  let φ : E →ₐ[F] Ω := IsAlgClosed.lift
  let ι : K →ₐ[F] Ω := IsScalarTower.toAlgHom F K Ω
  let x' := Units.map (Algebra.TensorProduct.map ι (AlgHom.id F B)).toMonoidHom x
  have hx' : x' ∈ unitaryPoints τ Ω := map_mem_unitaryPoints τ ι hx
  have hz' : (relativeNorm F E B Ω x' : E ⊗[F] Ω) = z ⊗ₜ[F] (1 : Ω) := by
    rw [relativeNorm_naturality]
    change Algebra.TensorProduct.map (AlgHom.id E E) ι (relativeNorm F E B K x : E ⊗[F] K) = _
    rw [hz, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have h := tensorProj_conjugation_relativeNorm τ hτ Ω φ x'
  rw [involutionUnits_eq_inv τ hx', map_inv, hz'] at h
  rw [map_units_inv, hz', HermitianMatrix.tensorProj_tmul, HermitianMatrix.tensorProj_tmul,
    mul_one, mul_one] at h
  have hz0 : φ z ≠ 0 := by
    intro h0
    have h1 := congrArg (HermitianMatrix.tensorProj F E φ) hz'
    have hu := (relativeNorm F E B Ω x').isUnit.map (HermitianMatrix.tensorProj F E φ)
    rw [h1, HermitianMatrix.tensorProj_tmul, mul_one, h0] at hu
    exact not_isUnit_zero hu
  apply φ.toRingHom.injective
  change φ (z * conjugation F E z) = φ 1
  rw [map_mul, map_one]
  change φ z * (φ.comp (conjugation F E).toAlgHom) z = 1
  rw [h, mul_inv_cancel₀ hz0]

end Conjugation

end Langlands.CentralSimple.UnitaryPoints
