import Langlands.Global.ArchimedeanCartanTraceDuality
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Polynomial evaluation and trace comparison on actual Cartan spaces -/

noncomputable section
universe u v w
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

private def symmetricMap {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) : SymmetricAlgebra ℂ V →ₐ[ℂ] SymmetricAlgebra ℂ W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ W).comp f)

@[simp]
private theorem symmetricMap_ι {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (X : V) :
    symmetricMap f (SymmetricAlgebra.ι ℂ V X) = SymmetricAlgebra.ι ℂ W (f X) :=
  SymmetricAlgebra.lift_ι_apply _ _

private def symmetricEquivalence {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) : SymmetricAlgebra ℂ V ≃ₐ[ℂ] SymmetricAlgebra ℂ W :=
  { symmetricMap e.toLinearMap with
    invFun := symmetricMap e.symm.toLinearMap
    left_inv := by
      have h : (symmetricMap e.symm.toLinearMap).comp (symmetricMap e.toLinearMap) =
          AlgHom.id ℂ (SymmetricAlgebra ℂ V) := by
        apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro X
        simp
      exact fun P => AlgHom.congr_fun h P
    right_inv := by
      have h : (symmetricMap e.toLinearMap).comp (symmetricMap e.symm.toLinearMap) =
          AlgHom.id ℂ (SymmetricAlgebra ℂ W) := by
        apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro X
        simp
      exact fun P => AlgHom.congr_fun h P }

@[simp]
private theorem symmetricEquivalence_ι {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (X : V) :
    symmetricEquivalence e (SymmetricAlgebra.ι ℂ V X) =
      SymmetricAlgebra.ι ℂ W (e X) :=
  symmetricMap_ι _ _

private theorem symmetric_lift_ext {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (P Q : SymmetricAlgebra ℂ V)
    (h : ∀ f : Module.Dual ℂ V, SymmetricAlgebra.lift f P = SymmetricAlgebra.lift f Q) :
    P = Q := by
  classical
  let b := Module.finBasis ℂ V
  have heval (f : Module.Dual ℂ V) (T : SymmetricAlgebra ℂ V) :
      SymmetricAlgebra.lift f T =
        MvPolynomial.eval (fun i => f (b i)) (SymmetricAlgebra.equivMvPolynomial b T) := by
    have hm : SymmetricAlgebra.lift f =
        (MvPolynomial.aeval (fun i => f (b i))).comp
          (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
      apply SymmetricAlgebra.algHom_ext
      apply b.ext
      intro i
      simp
    exact AlgHom.congr_fun hm T
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  apply MvPolynomial.funext
  intro t
  let f : Module.Dual ℂ V := b.constr ℂ t
  have hft (i) : f (b i) = t i := by simp [f]
  simpa only [heval, hft] using h f

private theorem dual_symmetric_ext {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (P Q : SymmetricAlgebra ℂ (Module.Dual ℂ V))
    (h : ∀ X : V, SymmetricAlgebra.lift (Module.Dual.eval ℂ V X) P =
      SymmetricAlgebra.lift (Module.Dual.eval ℂ V X) Q) : P = Q := by
  apply symmetric_lift_ext P Q
  intro f
  obtain ⟨X, hX⟩ := (Module.evalEquiv ℂ V).surjective f
  change Module.Dual.eval ℂ V X = f at hX
  rw [← hX]
  exact h X

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

/-- Polynomial tensors on the actual full complex Lie space. -/
abbrev LiePolynomialAlgebra :=
  SymmetricAlgebra ℂ (Module.Dual ℂ (ComplexLieAlgebra K n))

/-- Polynomial tensors on the actual complex Cartan complement. -/
abbrev CartanPolynomialAlgebra :=
  SymmetricAlgebra ℂ (Module.Dual ℂ (ComplexCartanComplement K n))

/-- Evaluation of polynomial tensors at an actual full vector. -/
def liePolynomialEvaluation (X : ComplexLieAlgebra K n) : LiePolynomialAlgebra K n →ₐ[ℂ] ℂ :=
  SymmetricAlgebra.lift (Module.Dual.eval ℂ (ComplexLieAlgebra K n) X)

/-- Evaluation of polynomial tensors at an actual complementary vector. -/
def cartanPolynomialEvaluation (X : ComplexCartanComplement K n) :
    CartanPolynomialAlgebra K n →ₐ[ℂ] ℂ :=
  SymmetricAlgebra.lift (Module.Dual.eval ℂ (ComplexCartanComplement K n) X)

omit [NumberField K] in
@[simp]
theorem liePolynomialEvaluation_ι (X : ComplexLieAlgebra K n)
    (f : Module.Dual ℂ (ComplexLieAlgebra K n)) :
    liePolynomialEvaluation K n X (SymmetricAlgebra.ι ℂ _ f) = f X :=
  SymmetricAlgebra.lift_ι_apply _ _

omit [NumberField K] in
@[simp]
theorem cartanPolynomialEvaluation_ι (X : ComplexCartanComplement K n)
    (f : Module.Dual ℂ (ComplexCartanComplement K n)) :
    cartanPolynomialEvaluation K n X (SymmetricAlgebra.ι ℂ _ f) = f X :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem liePolynomial_ext {P Q : LiePolynomialAlgebra K n}
    (h : ∀ X, liePolynomialEvaluation K n X P = liePolynomialEvaluation K n X Q) : P = Q :=
  dual_symmetric_ext P Q h

theorem cartanPolynomial_ext {P Q : CartanPolynomialAlgebra K n}
    (h : ∀ X, cartanPolynomialEvaluation K n X P = cartanPolynomialEvaluation K n X Q) :
    P = Q :=
  dual_symmetric_ext P Q h

/-- Lift the actual full trace-duality equivalence to symmetric algebras. -/
def lieSymmetricTraceEquiv : LieSymmetricAlgebra K n ≃ₐ[ℂ] LiePolynomialAlgebra K n :=
  symmetricEquivalence (complexTraceDualEquiv K n)

/-- Lift the actual complementary trace-duality equivalence to symmetric algebras. -/
def cartanSymmetricTraceEquiv : CartanSymmetricAlgebra K n ≃ₐ[ℂ] CartanPolynomialAlgebra K n :=
  symmetricEquivalence (cartanTraceDualEquiv K n)

@[simp]
theorem lieSymmetricTraceEquiv_ι (X : ComplexLieAlgebra K n) :
    lieSymmetricTraceEquiv K n (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (complexTraceDualEquiv K n X) :=
  symmetricEquivalence_ι _ _

@[simp]
theorem cartanSymmetricTraceEquiv_ι (X : ComplexCartanComplement K n) :
    cartanSymmetricTraceEquiv K n (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (cartanTraceDualEquiv K n X) :=
  symmetricEquivalence_ι _ _

/-- The restriction of polynomial tensors along the actual Cartan inclusion. -/
def cartanPolynomialRestriction : LiePolynomialAlgebra K n →ₐ[ℂ] CartanPolynomialAlgebra K n :=
  symmetricMap (cartanComplexInclusion K n).dualMap

omit [NumberField K] in
@[simp]
theorem cartanPolynomialRestriction_ι (f : Module.Dual ℂ (ComplexLieAlgebra K n)) :
    cartanPolynomialRestriction K n (SymmetricAlgebra.ι ℂ _ f) =
      SymmetricAlgebra.ι ℂ _ (f.comp (cartanComplexInclusion K n)) :=
  symmetricMap_ι _ _

/-- The actual vector projection becomes polynomial restriction under trace duality. -/
theorem cartanSymmetricTraceEquiv_projection (P : LieSymmetricAlgebra K n) :
    cartanSymmetricTraceEquiv K n (cartanSymmetricProjection K n P) =
      cartanPolynomialRestriction K n (lieSymmetricTraceEquiv K n P) := by
  have h : (cartanSymmetricTraceEquiv K n).toAlgHom.comp (cartanSymmetricProjection K n) =
      (cartanPolynomialRestriction K n).comp (lieSymmetricTraceEquiv K n).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    change cartanSymmetricTraceEquiv K n
        (cartanSymmetricProjection K n (SymmetricAlgebra.ι ℂ _ X)) =
      cartanPolynomialRestriction K n
        (lieSymmetricTraceEquiv K n (SymmetricAlgebra.ι ℂ _ X))
    simp [cartanTraceDualEquiv_projection]
  exact AlgHom.congr_fun h P

omit [NumberField K] in
theorem cartanPolynomialRestriction_evaluation (P : LiePolynomialAlgebra K n)
    (X : ComplexCartanComplement K n) :
    cartanPolynomialEvaluation K n X (cartanPolynomialRestriction K n P) =
      liePolynomialEvaluation K n (cartanComplexInclusion K n X) P := by
  have h : (cartanPolynomialEvaluation K n X).comp (cartanPolynomialRestriction K n) =
      liePolynomialEvaluation K n (cartanComplexInclusion K n X) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro f
    simp
  exact AlgHom.congr_fun h P

/-- Contragredient full-group conjugation lifted to polynomial tensors. -/
def liePolynomialConjugation (g : InfiniteAdelicGL K n) :
    LiePolynomialAlgebra K n ≃ₐ[ℂ] LiePolynomialAlgebra K n :=
  symmetricEquivalence (complexLieConjugation K n g⁻¹).toLinearEquiv.dualMap

/-- Contragredient full-compact conjugation lifted to complementary polynomials. -/
def cartanPolynomialConjugation (k : standardInfiniteCompact K n) :
    CartanPolynomialAlgebra K n ≃ₐ[ℂ] CartanPolynomialAlgebra K n :=
  symmetricEquivalence (cartanComplexConjugation K n k⁻¹).dualMap

omit [NumberField K] in
@[simp]
theorem liePolynomialConjugation_ι (g : InfiniteAdelicGL K n)
    (f : Module.Dual ℂ (ComplexLieAlgebra K n)) :
    liePolynomialConjugation K n g (SymmetricAlgebra.ι ℂ _ f) =
      SymmetricAlgebra.ι ℂ _ (f.comp (complexLieConjugation K n g⁻¹).toLinearMap) :=
  symmetricEquivalence_ι _ _

omit [NumberField K] in
@[simp]
theorem cartanPolynomialConjugation_ι (k : standardInfiniteCompact K n)
    (f : Module.Dual ℂ (ComplexCartanComplement K n)) :
    cartanPolynomialConjugation K n k (SymmetricAlgebra.ι ℂ _ f) =
      SymmetricAlgebra.ι ℂ _ (f.comp (cartanComplexConjugation K n k⁻¹).toLinearMap) :=
  symmetricEquivalence_ι _ _

omit [NumberField K] in
theorem liePolynomialConjugation_evaluation (g : InfiniteAdelicGL K n)
    (P : LiePolynomialAlgebra K n) (X : ComplexLieAlgebra K n) :
    liePolynomialEvaluation K n X (liePolynomialConjugation K n g P) =
      liePolynomialEvaluation K n (complexLieConjugation K n g⁻¹ X) P := by
  have h : (liePolynomialEvaluation K n X).comp
        (liePolynomialConjugation K n g).toAlgHom =
      liePolynomialEvaluation K n (complexLieConjugation K n g⁻¹ X) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro f
    simp
  exact AlgHom.congr_fun h P

omit [NumberField K] in
theorem cartanPolynomialConjugation_evaluation (k : standardInfiniteCompact K n)
    (P : CartanPolynomialAlgebra K n) (X : ComplexCartanComplement K n) :
    cartanPolynomialEvaluation K n X (cartanPolynomialConjugation K n k P) =
      cartanPolynomialEvaluation K n (cartanComplexConjugation K n k⁻¹ X) P := by
  have h : (cartanPolynomialEvaluation K n X).comp
        (cartanPolynomialConjugation K n k).toAlgHom =
      cartanPolynomialEvaluation K n (cartanComplexConjugation K n k⁻¹ X) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro f
    simp
  exact AlgHom.congr_fun h P

@[simp]
theorem liePolynomialConjugation_one :
    liePolynomialConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro P
  apply liePolynomial_ext K n
  intro X
  simp [liePolynomialConjugation_evaluation]

theorem liePolynomialConjugation_mul (g h : InfiniteAdelicGL K n) :
    liePolynomialConjugation K n (g * h) =
      (liePolynomialConjugation K n h).trans (liePolynomialConjugation K n g) := by
  apply AlgEquiv.ext
  intro P
  apply liePolynomial_ext K n
  intro X
  simp [liePolynomialConjugation_evaluation, complexLieConjugation_mul]

@[simp]
theorem liePolynomialConjugation_inv (g : InfiniteAdelicGL K n) :
    liePolynomialConjugation K n g⁻¹ = (liePolynomialConjugation K n g).symm := by
  apply AlgEquiv.ext
  intro P
  apply (liePolynomialConjugation K n g).injective
  have h := congrArg (fun e : LiePolynomialAlgebra K n ≃ₐ[ℂ]
    LiePolynomialAlgebra K n => e P) (liePolynomialConjugation_mul K n g g⁻¹)
  simpa using h.symm

@[simp]
theorem cartanPolynomialConjugation_one :
    cartanPolynomialConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro P
  apply cartanPolynomial_ext K n
  intro X
  simp [cartanPolynomialConjugation_evaluation]

theorem cartanPolynomialConjugation_mul (k l : standardInfiniteCompact K n) :
    cartanPolynomialConjugation K n (k * l) =
      (cartanPolynomialConjugation K n l).trans (cartanPolynomialConjugation K n k) := by
  apply AlgEquiv.ext
  intro P
  apply cartanPolynomial_ext K n
  intro X
  simp [cartanPolynomialConjugation_evaluation, cartanComplexConjugation_mul]

@[simp]
theorem cartanPolynomialConjugation_inv (k : standardInfiniteCompact K n) :
    cartanPolynomialConjugation K n k⁻¹ = (cartanPolynomialConjugation K n k).symm := by
  apply AlgEquiv.ext
  intro P
  apply (cartanPolynomialConjugation K n k).injective
  have h := congrArg (fun e : CartanPolynomialAlgebra K n ≃ₐ[ℂ]
    CartanPolynomialAlgebra K n => e P) (cartanPolynomialConjugation_mul K n k k⁻¹)
  simpa using h.symm

theorem cartanPolynomialRestriction_conjugation (k : standardInfiniteCompact K n)
    (P : LiePolynomialAlgebra K n) :
    cartanPolynomialRestriction K n (liePolynomialConjugation K n k.val P) =
      cartanPolynomialConjugation K n k (cartanPolynomialRestriction K n P) := by
  apply cartanPolynomial_ext K n
  intro X
  simp only [cartanPolynomialRestriction_evaluation, liePolynomialConjugation_evaluation,
    cartanPolynomialConjugation_evaluation, cartanComplexInclusion_conjugation,
    Subgroup.coe_inv]

theorem lieSymmetricTraceEquiv_conjugation (g : InfiniteAdelicGL K n)
    (P : LieSymmetricAlgebra K n) :
    lieSymmetricTraceEquiv K n (lieSymmetricConjugation K n g P) =
      liePolynomialConjugation K n g (lieSymmetricTraceEquiv K n P) := by
  have h : (lieSymmetricTraceEquiv K n).toAlgHom.comp
        (lieSymmetricConjugation K n g).toAlgHom =
      (liePolynomialConjugation K n g).toAlgHom.comp
        (lieSymmetricTraceEquiv K n).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    simp [complexTraceDualEquiv_conjugation]
  exact AlgHom.congr_fun h P

theorem cartanSymmetricTraceEquiv_conjugation (k : standardInfiniteCompact K n)
    (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricTraceEquiv K n (cartanSymmetricConjugation K n k P) =
      cartanPolynomialConjugation K n k (cartanSymmetricTraceEquiv K n P) := by
  have h : (cartanSymmetricTraceEquiv K n).toAlgHom.comp
        (cartanSymmetricConjugation K n k).toAlgHom =
      (cartanPolynomialConjugation K n k).toAlgHom.comp
        (cartanSymmetricTraceEquiv K n).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    simp [cartanTraceDualEquiv_conjugation]
  exact AlgHom.congr_fun h P

end Langlands.Global.ArchimedeanGL
