import Langlands.Global.ArchimedeanCartanPolynomialDuality
import Langlands.Global.ArchimedeanCartanSymmetricInvariants
import Mathlib.Analysis.Matrix.Spectrum

/-! # Real evaluation and diagonal restriction on actual Cartan spaces -/

noncomputable section
universe u v
open scoped TensorProduct
open NumberField
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

private theorem complexified_dual_symmetric_ext_real
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (P Q : SymmetricAlgebra ℂ (Module.Dual ℂ (ℂ ⊗[ℝ] V)))
    (h : ∀ X : V,
      SymmetricAlgebra.lift (Module.Dual.eval ℂ (ℂ ⊗[ℝ] V) (1 ⊗ₜ[ℝ] X)) P =
        SymmetricAlgebra.lift (Module.Dual.eval ℂ (ℂ ⊗[ℝ] V) (1 ⊗ₜ[ℝ] X)) Q) :
    P = Q := by
  classical
  let b := Module.finBasis ℝ V
  let d := (b.baseChange ℂ).dualBasis
  have heval (X : ℂ ⊗[ℝ] V)
      (T : SymmetricAlgebra ℂ (Module.Dual ℂ (ℂ ⊗[ℝ] V))) :
      SymmetricAlgebra.lift (Module.Dual.eval ℂ (ℂ ⊗[ℝ] V) X) T =
        MvPolynomial.eval (fun i => d i X) (SymmetricAlgebra.equivMvPolynomial d T) := by
    have hm : SymmetricAlgebra.lift (Module.Dual.eval ℂ (ℂ ⊗[ℝ] V) X) =
        (MvPolynomial.aeval (fun i => d i X)).comp
          (SymmetricAlgebra.equivMvPolynomial d).toAlgHom := by
      apply SymmetricAlgebra.algHom_ext
      apply d.ext
      intro i
      simp
    exact AlgHom.congr_fun hm T
  apply (SymmetricAlgebra.equivMvPolynomial d).injective
  apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro t ht
  choose r hr using fun i => ht i (Set.mem_univ i)
  let X : V := ∑ i, r i • b i
  have hcoord (i) : d i (1 ⊗ₜ[ℝ] X) = t i := by
    change (b.baseChange ℂ).dualBasis i (1 ⊗ₜ[ℝ] X) = t i
    rw [Module.Basis.dualBasis_apply, Module.Basis.baseChange_repr_tmul]
    have hx : b.repr X i = r i := by simp [X, Finsupp.single_apply]
    rw [hx]
    simpa using hr i
  simpa only [heval, hcoord] using h X

variable (K : Type u) [Field K] (n : ℕ)

local instance [NumberField K] : FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

theorem liePolynomial_ext_real [NumberField K] {P Q : LiePolynomialAlgebra K n}
    (h : ∀ X : RealLieAlgebra K n,
      liePolynomialEvaluation K n (1 ⊗ₜ[ℝ] X) P =
        liePolynomialEvaluation K n (1 ⊗ₜ[ℝ] X) Q) : P = Q :=
  complexified_dual_symmetric_ext_real P Q h

theorem cartanPolynomial_ext_real [NumberField K] {P Q : CartanPolynomialAlgebra K n}
    (h : ∀ X : cartanComplement K n,
      cartanPolynomialEvaluation K n (1 ⊗ₜ[ℝ] X) P =
        cartanPolynomialEvaluation K n (1 ⊗ₜ[ℝ] X) Q) : P = Q :=
  complexified_dual_symmetric_ext_real P Q h

/-- Real diagonal coordinates at all infinite places, also at the complex places. -/
abbrev RealCartanDiagonal :=
  ({v : InfinitePlace K // v.IsReal} → Fin n → ℝ) ×
    ({v : InfinitePlace K // v.IsComplex} → Fin n → ℝ)

/-- Include real diagonal matrices in the actual self-adjoint Cartan complement. -/
def cartanDiagonalInclusion : RealCartanDiagonal K n →ₗ[ℝ] cartanComplement K n where
  toFun t := ⟨(realLieAlgebraToMatrix K n).symm
      (Matrix.diagonal (fun i => (fun v => t.1 v i, fun v => (t.2 v i : ℂ)))),
    by
      rw [mem_cartanComplement_iff_coordinates]
      constructor
      · intro v i j
        by_cases hij : i = j <;> simp [hij, eq_comm]
      · intro v i j
        by_cases hij : i = j <;> simp [hij, eq_comm]⟩
  map_add' t s := by
    apply Subtype.ext
    apply (realLieAlgebraToMatrix K n).injective
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      by_cases hij : i = j <;> simp [hij]
    · funext v
      by_cases hij : i = j <;> simp [hij]
  map_smul' r t := by
    apply Subtype.ext
    apply (realLieAlgebraToMatrix K n).injective
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      by_cases hij : i = j <;> simp [hij]
    · funext v
      by_cases hij : i = j <;> simp [hij]

@[simp]
theorem cartanDiagonalInclusion_matrix (t : RealCartanDiagonal K n) :
    realLieAlgebraToMatrix K n (cartanDiagonalInclusion K n t) =
      Matrix.diagonal (fun i => (fun v => t.1 v i, fun v => (t.2 v i : ℂ))) := rfl

theorem cartanDiagonalInclusion_injective :
    Function.Injective (cartanDiagonalInclusion K n) := by
  intro t s h
  have hm := congrArg (fun X : cartanComplement K n =>
    realLieAlgebraToMatrix K n X) h
  apply Prod.ext
  · funext v i
    simpa using congrArg (fun A => (A i i).1 v) hm
  · funext v i
    apply Complex.ofReal_injective
    simpa using congrArg (fun A => (A i i).2 v) hm

/-- Complex scalar extension of the actual real diagonal space. -/
abbrev ComplexCartanDiagonal := ℂ ⊗[ℝ] RealCartanDiagonal K n

/-- Scalar extension of the real diagonal inclusion. -/
def cartanDiagonalComplexInclusion :
    ComplexCartanDiagonal K n →ₗ[ℂ] ComplexCartanComplement K n :=
  (cartanDiagonalInclusion K n).baseChange ℂ

@[simp]
theorem cartanDiagonalComplexInclusion_tmul (z : ℂ) (t : RealCartanDiagonal K n) :
    cartanDiagonalComplexInclusion K n (z ⊗ₜ[ℝ] t) =
      z ⊗ₜ[ℝ] cartanDiagonalInclusion K n t := rfl

theorem cartanDiagonalComplexInclusion_injective :
    Function.Injective (cartanDiagonalComplexInclusion K n) :=
  Module.Flat.lTensor_preserves_injective_linearMap (cartanDiagonalInclusion K n)
    (cartanDiagonalInclusion_injective K n)

private def realMatrixProjection (v : {v : InfinitePlace K // v.IsReal}) :
    ArchimedeanMatrix K n →+* Matrix (Fin n) (Fin n) ℝ :=
  ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsReal} => ℝ) v).comp
    (RingHom.fst _ _)).mapMatrix

private def complexMatrixProjection (v : {v : InfinitePlace K // v.IsComplex}) :
    ArchimedeanMatrix K n →+* Matrix (Fin n) (Fin n) ℂ :=
  ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsComplex} => ℂ) v).comp
    (RingHom.snd _ _)).mapMatrix

private theorem realMatrixProjection_conjugation_factors
    (p : ArchimedeanCompactFactors K n) (X : RealLieAlgebra K n)
    (v : {v : InfinitePlace K // v.IsReal}) :
    realMatrixProjection K n v (realLieAlgebraToMatrix K n
      (realLieConjugation K n (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p) X)) =
      (p.1 v).val * realMatrixProjection K n v (realLieAlgebraToMatrix K n X) *
        ((p.1 v)⁻¹).val := by
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul,
    ← map_inv, ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

private theorem complexMatrixProjection_conjugation_factors
    (p : ArchimedeanCompactFactors K n) (X : RealLieAlgebra K n)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    complexMatrixProjection K n v (realLieAlgebraToMatrix K n
      (realLieConjugation K n (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p) X)) =
      (p.2 v).val * complexMatrixProjection K n v (realLieAlgebraToMatrix K n X) *
        ((p.2 v)⁻¹).val := by
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul,
    ← map_inv, ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

private theorem realMatrixProjection_diagonal (t : RealCartanDiagonal K n)
    (v : {v : InfinitePlace K // v.IsReal}) :
    realMatrixProjection K n v
      (realLieAlgebraToMatrix K n (cartanDiagonalInclusion K n t)) =
        Matrix.diagonal (t.1 v) := by
  rw [cartanDiagonalInclusion_matrix]
  apply Matrix.ext
  intro i j
  change (Matrix.diagonal
    (fun i => (fun v => t.1 v i, fun v => (t.2 v i : ℂ))) i j).1 v = _
  by_cases hij : i = j <;> simp [hij]

private theorem complexMatrixProjection_diagonal (t : RealCartanDiagonal K n)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    complexMatrixProjection K n v
      (realLieAlgebraToMatrix K n (cartanDiagonalInclusion K n t)) =
        Matrix.diagonal (fun i => (t.2 v i : ℂ)) := by
  rw [cartanDiagonalInclusion_matrix]
  apply Matrix.ext
  intro i j
  change (Matrix.diagonal
    (fun i => (fun v => t.1 v i, fun v => (t.2 v i : ℂ))) i j).2 v = _
  by_cases hij : i = j <;> simp [hij]

/-- Every actual self-adjoint Cartan vector is compact conjugate to a real diagonal. -/
theorem cartanRealConjugation_diagonal (X : cartanComplement K n) :
    ∃ (k : standardInfiniteCompact K n) (t : RealCartanDiagonal K n),
      cartanRealConjugation K n k (cartanDiagonalInclusion K n t) = X := by
  classical
  let Ar := fun v => realMatrixProjection K n v (realLieAlgebraToMatrix K n X)
  let Ac := fun v => complexMatrixProjection K n v (realLieAlgebraToMatrix K n X)
  have hr (v : {v : InfinitePlace K // v.IsReal}) : (Ar v).IsHermitian := by
    apply Matrix.ext
    intro i j
    change (realLieAlgebraToMatrix K n X j i).1 v =
      (realLieAlgebraToMatrix K n X i j).1 v
    exact ((mem_cartanComplement_iff_coordinates K n X).mp X.property).1 v i j
  have hc (v : {v : InfinitePlace K // v.IsComplex}) : (Ac v).IsHermitian := by
    apply Matrix.ext
    intro i j
    change star ((realLieAlgebraToMatrix K n X j i).2 v) =
      (realLieAlgebraToMatrix K n X i j).2 v
    exact ((mem_cartanComplement_iff_coordinates K n X).mp X.property).2 v i j
  let p : ArchimedeanCompactFactors K n :=
    (fun v => (hr v).eigenvectorUnitary, fun v => (hc v).eigenvectorUnitary)
  let t : RealCartanDiagonal K n :=
    (fun v => (hr v).eigenvalues, fun v => (hc v).eigenvalues)
  let k : standardInfiniteCompact K n :=
    ⟨ArchimedeanCompactFactors.toInfiniteAdelicGL K n p, ⟨p, rfl⟩⟩
  refine ⟨k, t, ?_⟩
  apply Subtype.ext
  apply (realLieAlgebraToMatrix K n).injective
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    have h : realMatrixProjection K n v
        (realLieAlgebraToMatrix K n
          (cartanRealConjugation K n k (cartanDiagonalInclusion K n t))) = Ar v := by
      change realMatrixProjection K n v
        (realLieAlgebraToMatrix K n (realLieConjugation K n
          (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p)
          (cartanDiagonalInclusion K n t))) = Ar v
      rw [realMatrixProjection_conjugation_factors, realMatrixProjection_diagonal]
      simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, p, t]
        using (hr v).spectral_theorem.symm
    exact congrArg (fun A => A i j) h
  · funext v
    have h : complexMatrixProjection K n v
        (realLieAlgebraToMatrix K n
          (cartanRealConjugation K n k (cartanDiagonalInclusion K n t))) = Ac v := by
      change complexMatrixProjection K n v
        (realLieAlgebraToMatrix K n (realLieConjugation K n
          (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p)
          (cartanDiagonalInclusion K n t))) = Ac v
      rw [complexMatrixProjection_conjugation_factors, complexMatrixProjection_diagonal]
      simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, p, t]
        using (hc v).spectral_theorem.symm
    exact congrArg (fun A => A i j) h

/-- Polynomial functions on the actual complexified real diagonal space. -/
abbrev CartanDiagonalPolynomialAlgebra :=
  SymmetricAlgebra ℂ (Module.Dual ℂ (ComplexCartanDiagonal K n))

/-- Evaluate a diagonal polynomial tensor at an actual diagonal vector. -/
def cartanDiagonalPolynomialEvaluation (t : ComplexCartanDiagonal K n) :
    CartanDiagonalPolynomialAlgebra K n →ₐ[ℂ] ℂ :=
  SymmetricAlgebra.lift (Module.Dual.eval ℂ (ComplexCartanDiagonal K n) t)

@[simp]
theorem cartanDiagonalPolynomialEvaluation_ι (t : ComplexCartanDiagonal K n)
    (f : Module.Dual ℂ (ComplexCartanDiagonal K n)) :
    cartanDiagonalPolynomialEvaluation K n t (SymmetricAlgebra.ι ℂ _ f) = f t :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Restrict complementary polynomial functions to the actual diagonal subspace. -/
def cartanDiagonalPolynomialRestriction :
    CartanPolynomialAlgebra K n →ₐ[ℂ] CartanDiagonalPolynomialAlgebra K n :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℂ (Module.Dual ℂ (ComplexCartanDiagonal K n))).comp
      (cartanDiagonalComplexInclusion K n).dualMap)

@[simp]
theorem cartanDiagonalPolynomialRestriction_ι
    (f : Module.Dual ℂ (ComplexCartanComplement K n)) :
    cartanDiagonalPolynomialRestriction K n (SymmetricAlgebra.ι ℂ _ f) =
      SymmetricAlgebra.ι ℂ _ (f.comp (cartanDiagonalComplexInclusion K n)) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem cartanDiagonalPolynomialRestriction_evaluation (P : CartanPolynomialAlgebra K n)
    (t : ComplexCartanDiagonal K n) :
    cartanDiagonalPolynomialEvaluation K n t (cartanDiagonalPolynomialRestriction K n P) =
      cartanPolynomialEvaluation K n (cartanDiagonalComplexInclusion K n t) P := by
  have h : (cartanDiagonalPolynomialEvaluation K n t).comp
      (cartanDiagonalPolynomialRestriction K n) =
      cartanPolynomialEvaluation K n (cartanDiagonalComplexInclusion K n t) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro f
    simp
  exact AlgHom.congr_fun h P

theorem cartanDiagonalPolynomialRestriction_injective_on_invariants [NumberField K]
    {P Q : CartanPolynomialAlgebra K n}
    (hP : ∀ k : standardInfiniteCompact K n, cartanPolynomialConjugation K n k P = P)
    (hQ : ∀ k : standardInfiniteCompact K n, cartanPolynomialConjugation K n k Q = Q)
    (h : cartanDiagonalPolynomialRestriction K n P =
      cartanDiagonalPolynomialRestriction K n Q) : P = Q := by
  apply cartanPolynomial_ext_real K n
  intro X
  obtain ⟨k, t, ht⟩ := cartanRealConjugation_diagonal K n X
  have hPX := congrArg
    (cartanPolynomialEvaluation K n (1 ⊗ₜ[ℝ] cartanDiagonalInclusion K n t)) (hP k⁻¹)
  have hQX := congrArg
    (cartanPolynomialEvaluation K n (1 ⊗ₜ[ℝ] cartanDiagonalInclusion K n t)) (hQ k⁻¹)
  rw [cartanPolynomialConjugation_evaluation] at hPX hQX
  simp only [inv_inv, cartanComplexConjugation_tmul, ht] at hPX hQX
  rw [hPX, hQX]
  have he := congrArg (cartanDiagonalPolynomialEvaluation K n (1 ⊗ₜ[ℝ] t)) h
  simpa only [cartanDiagonalPolynomialRestriction_evaluation,
    cartanDiagonalComplexInclusion_tmul] using he

/-- Restrict actual compact-fixed symmetric tensors, using trace duality, to diagonals. -/
def cartanCompactInvariantDiagonalRestriction [NumberField K] :
    cartanSymmetricCompactInvariants K n →ₐ[ℂ] CartanDiagonalPolynomialAlgebra K n :=
  (cartanDiagonalPolynomialRestriction K n).comp
    ((cartanSymmetricTraceEquiv K n).toAlgHom.comp
      (cartanSymmetricCompactInvariants K n).val)

@[simp]
theorem cartanCompactInvariantDiagonalRestriction_apply [NumberField K]
    (P : cartanSymmetricCompactInvariants K n) :
    cartanCompactInvariantDiagonalRestriction K n P =
      cartanDiagonalPolynomialRestriction K n (cartanSymmetricTraceEquiv K n P.val) := rfl

/-- Actual compact invariants are determined by their diagonal polynomial restriction. -/
theorem cartanCompactInvariantDiagonalRestriction_injective [NumberField K] :
    Function.Injective (cartanCompactInvariantDiagonalRestriction K n) := by
  intro P Q h
  apply Subtype.ext
  apply (cartanSymmetricTraceEquiv K n).injective
  apply cartanDiagonalPolynomialRestriction_injective_on_invariants K n
  · intro k
    rw [← cartanSymmetricTraceEquiv_conjugation, P.property k]
  · intro k
    rw [← cartanSymmetricTraceEquiv_conjugation, Q.property k]
  · exact h

end Langlands.Global.ArchimedeanGL
