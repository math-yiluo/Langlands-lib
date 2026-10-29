import Langlands.Shimura.PEL.RegularHodge
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The homogeneous determinant of the regular Hodge representation -/

noncomputable section
universe u v w t s
open scoped TensorProduct
open MvPolynomial

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Fintype ι]
    {κ : Type t} [Fintype κ] [DecidableEq κ]

/-- The matrix of the universal linear combination of a family of endomorphisms. -/
def matrix (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    Matrix κ κ (MvPolynomial ι R) :=
  fun j k => ∑ i, C (LinearMap.toMatrix b b (f i) j k) * X i

/-- The determinant polynomial is computed from the given actual endomorphisms. -/
def polynomial (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    MvPolynomial ι R :=
  (matrix b f).det

theorem matrix_isHomogeneous (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (j k : κ) :
    (matrix b f j k).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

omit [Fintype ι] in
/-- The determinant of a matrix of linear homogeneous entries has its usual degree. -/
theorem det_isHomogeneous (P : Matrix κ κ (MvPolynomial ι R))
    (hP : ∀ j k, (P j k).IsHomogeneous 1) :
    P.det.IsHomogeneous (Fintype.card κ) := by
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hp : (∏ i, P (σ i) i).IsHomogeneous (Fintype.card κ) := by
    simpa using IsHomogeneous.prod Finset.univ (fun i => P (σ i) i)
      (fun _ => 1) (fun i _ => hP (σ i) i)
  simpa using hp.C_mul (((Equiv.Perm.sign σ : ℤ) : R))

theorem polynomial_isHomogeneous (b : Module.Basis κ R M)
    (f : ι → Module.End R M) :
    (polynomial b f).IsHomogeneous (Fintype.card κ) :=
  det_isHomogeneous _ (matrix_isHomogeneous b f)

theorem eval_matrix (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (x : ι → R) :
    (matrix b f).map (eval x) =
      LinearMap.toMatrix b b (∑ i, x i • f i) := by
  ext j k
  simp [matrix, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_comm]

/-- Evaluation recovers the determinant on the original module. -/
theorem eval_polynomial (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (x : ι → R) :
    eval x (polynomial b f) = LinearMap.det (∑ i, x i • f i) := by
  rw [polynomial, RingHom.map_det]
  change ((matrix b f).map (eval x)).det = _
  rw [eval_matrix, LinearMap.det_toMatrix]

/-- The same polynomial may be evaluated in any commutative coefficient algebra. -/
theorem eval₂_polynomial {S : Type s} [CommRing S]
    (g : R →+* S) (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (x : ι → S) :
    eval₂ g x (polynomial b f) =
      (∑ i, x i • (LinearMap.toMatrix b b (f i)).map g).det := by
  change (eval₂Hom g x) (matrix b f).det = _
  rw [RingHom.map_det]
  congr 1
  ext j k
  simp [matrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- Over an infinite domain the polynomial is independent of a module basis. -/
theorem polynomial_basis_independent [IsDomain R] [Infinite R]
    {κ' : Type s} [Fintype κ'] [DecidableEq κ']
    (b : Module.Basis κ R M) (b' : Module.Basis κ' R M)
    (f : ι → Module.End R M) :
    polynomial b f = polynomial b' f := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomial, eval_polynomial]

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.Shimura.RegularHodge

variable {B : Type u} [Ring B] [Algebra ℝ B]
    (h : ℂ →ₐ[ℝ] B) [FiniteDimensional ℝ B]
    {ι : Type v} [Fintype ι]

/-- The homogeneous determinant on the constructed identity Hodge summand. -/
def determinantPolynomial (a : ι → ℂ ⊗[ℝ] B) : MvPolynomial ι ℂ :=
  HodgeDeterminant.polynomial (Module.finBasis ℂ (submodule h))
    (fun i => leftAction h (a i))

theorem determinantPolynomial_isHomogeneous (a : ι → ℂ ⊗[ℝ] B) :
    (determinantPolynomial h a).IsHomogeneous
      (Module.finrank ℂ (submodule h)) := by
  simpa only [determinantPolynomial, Fintype.card_fin] using
    HodgeDeterminant.polynomial_isHomogeneous
      (Module.finBasis ℂ (submodule h)) (fun i => leftAction h (a i))

/-- This is the determinant of the actual linear combination acting on `V₁`. -/
theorem eval_determinantPolynomial (a : ι → ℂ ⊗[ℝ] B) (x : ι → ℂ) :
    eval x (determinantPolynomial h a) =
      LinearMap.det (leftAction h (∑ i, x i • a i)) := by
  rw [determinantPolynomial, HodgeDeterminant.eval_polynomial]
  congr 1
  simp only [map_sum, map_smul]

/-- Any basis of the actual Hodge summand computes the same polynomial. -/
theorem determinantPolynomial_eq_basis {κ : Type w}
    [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℂ (submodule h)) (a : ι → ℂ ⊗[ℝ] B) :
    determinantPolynomial h a =
      HodgeDeterminant.polynomial b (fun i => leftAction h (a i)) :=
  HodgeDeterminant.polynomial_basis_independent _ _ _

end Langlands.Shimura.RegularHodge

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra
variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    {ι : Type t} [Fintype ι]

/-- Kottwitz's homogeneous polynomial for a finite family in the rational algebra. -/
def kottwitzHodgeDeterminant (a : ι → A) : MvPolynomial ι ℂ := by
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact RegularHodge.determinantPolynomial (D.realPositiveKottwitzHom C).val.hom
    (fun i => (1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a i))

theorem kottwitzHodgeDeterminant_isHomogeneous (a : ι → A) :
    (D.kottwitzHodgeDeterminant C a).IsHomogeneous
      (Module.finrank ℂ (D.kottwitzHodgeModule C)) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact RegularHodge.determinantPolynomial_isHomogeneous _ _

theorem eval_kottwitzHodgeDeterminant (a : ι → A) (x : ι → ℂ) :
    eval x (D.kottwitzHodgeDeterminant C a) =
      LinearMap.det (D.kottwitzHodgeAction C
        (∑ i, x i • ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a i)))) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact RegularHodge.eval_determinantPolynomial _ _ _

end Langlands.Shimura.CentralSimpleUnitaryData
