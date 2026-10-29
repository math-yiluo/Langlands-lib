import Langlands.Global.ArchimedeanCartanSymbol
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Ambient matrix realization of genuine Cartan polynomial actions -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
open Set Filter Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The full Hessian term and first-order moving-frame correction on ambient functions. -/
def cartanAmbientOperator (F : ArchimedeanMatrix K n → ℂ) :
    ArchimedeanMatrix K n → ℂ :=
  fun y => ∑ i : CartanBasisIndex K n,
    (fderiv ℝ (fderiv ℝ F) y
      (y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))
      (y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)) +
    fderiv ℝ F y
      (y * (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i) *
        realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))))

/-- The finite complex coefficient sum of ambient Cartan iterates, including the identity iterate. -/
def cartanAmbientPolynomial (p : Polynomial ℂ) (F : ArchimedeanMatrix K n → ℂ) :
    ArchimedeanMatrix K n → ℂ :=
  p.sum fun m c => c • ((cartanAmbientOperator K n)^[m] F)

/-- Any ambient extension agreeing on units realizes the genuine full square-sum action there. -/
theorem cartanAmbientOperator_eq_of_extension (f : SmoothFunctions K n)
    (F : ArchimedeanMatrix K n → ℂ)
    (hF : ∀ g : ArchimedeanGL K n,
      F (g : ArchimedeanMatrix K n) = f.val ((archimedeanGLCoordinates K n).symm g))
    (g : ArchimedeanGL K n) :
    cartanAmbientOperator K n F (g : ArchimedeanMatrix K n) =
      (envelopingAction K n (cartanSquareSum K n) f).val
        ((archimedeanGLCoordinates K n).symm g) := by
  have heq : F =ᶠ[𝓝 (g : ArchimedeanMatrix K n)] coordinateExtension K n f := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (g : ArchimedeanMatrix K n) ∈
        Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) from ⟨g, rfl⟩)]
      with y hy
    obtain ⟨h, rfl⟩ := hy
    rw [coordinateExtension_apply]
    exact hF h
  have hfirst := heq.fderiv_eq (𝕜 := ℝ)
  have hsecond := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  calc
    cartanAmbientOperator K n F (g : ArchimedeanMatrix K n) =
        cartanAmbientOperator K n (coordinateExtension K n f)
          (g : ArchimedeanMatrix K n) := by
      simp only [cartanAmbientOperator, hfirst, hsecond]
    _ = _ := by
      symm
      simpa only [cartanAmbientOperator, ContinuousMulEquiv.apply_symm_apply] using
        envelopingAction_cartanSquareSum_apply K n f ((archimedeanGLCoordinates K n).symm g)

/-- Repeated ambient application realizes every genuine enveloping power on units. -/
theorem cartanAmbientOperator_iterate_eq_of_extension (f : SmoothFunctions K n)
    (F : ArchimedeanMatrix K n → ℂ)
    (hF : ∀ g : ArchimedeanGL K n,
      F (g : ArchimedeanMatrix K n) = f.val ((archimedeanGLCoordinates K n).symm g)) :
    ∀ (m : ℕ) (g : ArchimedeanGL K n),
      ((cartanAmbientOperator K n)^[m] F) (g : ArchimedeanMatrix K n) =
        (envelopingAction K n ((cartanSquareSum K n) ^ m) f).val
          ((archimedeanGLCoordinates K n).symm g) := by
  intro m
  induction m with
  | zero =>
    intro g
    simpa only [Function.iterate_zero, id_eq, pow_zero, envelopingAction_one] using hF g
  | succ m ih =>
    intro g
    rw [Function.iterate_succ_apply']
    rw [cartanAmbientOperator_eq_of_extension K n
      (envelopingAction K n ((cartanSquareSum K n) ^ m) f)
      ((cartanAmbientOperator K n)^[m] F) ih g]
    rw [pow_succ', envelopingAction_mul]

/-- The finite ambient coefficient sum equals genuine enveloping polynomial evaluation on units. -/
theorem cartanAmbientPolynomial_eq_of_extension (f : SmoothFunctions K n)
    (F : ArchimedeanMatrix K n → ℂ)
    (hF : ∀ g : ArchimedeanGL K n,
      F (g : ArchimedeanMatrix K n) = f.val ((archimedeanGLCoordinates K n).symm g))
    (p : Polynomial ℂ) (g : ArchimedeanGL K n) :
    cartanAmbientPolynomial K n p F (g : ArchimedeanMatrix K n) =
      (envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) f).val
        ((archimedeanGLCoordinates K n).symm g) := by
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_endomorphism]
  simp only [cartanAmbientPolynomial, Polynomial.sum, Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [cartanAmbientOperator_iterate_eq_of_extension K n f F hF m g, map_pow]

/-- The published coordinate extension realizes the genuine square-sum action on units. -/
theorem cartanAmbientOperator_coordinateExtension (f : SmoothFunctions K n)
    (g : ArchimedeanGL K n) :
    cartanAmbientOperator K n (coordinateExtension K n f) (g : ArchimedeanMatrix K n) =
      (envelopingAction K n (cartanSquareSum K n) f).val
        ((archimedeanGLCoordinates K n).symm g) :=
  cartanAmbientOperator_eq_of_extension K n f _ (coordinateExtension_apply K n f) g

/-- Every ambient iterate of the coordinate extension realizes the genuine power on units. -/
theorem cartanAmbientOperator_iterate_coordinateExtension (f : SmoothFunctions K n)
    (m : ℕ) (g : ArchimedeanGL K n) :
    ((cartanAmbientOperator K n)^[m] (coordinateExtension K n f))
        (g : ArchimedeanMatrix K n) =
      (envelopingAction K n ((cartanSquareSum K n) ^ m) f).val
        ((archimedeanGLCoordinates K n).symm g) :=
  cartanAmbientOperator_iterate_eq_of_extension K n f _ (coordinateExtension_apply K n f) m g

/-- Every ambient polynomial expression of the coordinate extension realizes the genuine
polynomial action on units. -/
theorem cartanAmbientPolynomial_coordinateExtension (f : SmoothFunctions K n)
    (p : Polynomial ℂ) (g : ArchimedeanGL K n) :
    cartanAmbientPolynomial K n p (coordinateExtension K n f) (g : ArchimedeanMatrix K n) =
      (envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) f).val
        ((archimedeanGLCoordinates K n).symm g) :=
  cartanAmbientPolynomial_eq_of_extension K n f _ (coordinateExtension_apply K n f) p g

/-- A constant polynomial multiplies the transported smooth function by its constant on units. -/
theorem cartanAmbientPolynomial_C_coordinateExtension (f : SmoothFunctions K n) (c : ℂ)
    (g : ArchimedeanGL K n) :
    cartanAmbientPolynomial K n (Polynomial.C c) (coordinateExtension K n f)
        (g : ArchimedeanMatrix K n) =
      c * f.val ((archimedeanGLCoordinates K n).symm g) := by
  rw [cartanAmbientPolynomial_coordinateExtension, Polynomial.aeval_C, AlgHom.commutes,
    Module.algebraMap_end_apply]
  rfl

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (f : SmoothFunctions K n)
    (F : ArchimedeanMatrix K n → ℂ),
    (∀ g : ArchimedeanGL K n,
      F (g : ArchimedeanMatrix K n) = f.val ((archimedeanGLCoordinates K n).symm g)) →
    ∀ (p : Polynomial ℂ) (g : ArchimedeanGL K n),
      cartanAmbientPolynomial K n p F (g : ArchimedeanMatrix K n) =
        (envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) f).val
          ((archimedeanGLCoordinates K n).symm g) :=
  @cartanAmbientPolynomial_eq_of_extension

/-- The order-zero iterate is covered by the iterate theorem. -/
example (f : SmoothFunctions K n) (g : ArchimedeanGL K n) :
    ((cartanAmbientOperator K n)^[0] (coordinateExtension K n f))
        (g : ArchimedeanMatrix K n) =
      (envelopingAction K n ((cartanSquareSum K n) ^ 0) f).val
        ((archimedeanGLCoordinates K n).symm g) :=
  cartanAmbientOperator_iterate_coordinateExtension K n f 0 g

/-- The zero polynomial is covered by the polynomial theorem. -/
example (f : SmoothFunctions K n) (g : ArchimedeanGL K n) :
    cartanAmbientPolynomial K n 0 (coordinateExtension K n f) (g : ArchimedeanMatrix K n) =
      (envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) (0 : Polynomial ℂ)) f).val
        ((archimedeanGLCoordinates K n).symm g) :=
  cartanAmbientPolynomial_coordinateExtension K n f 0 g

end Langlands.Global.ArchimedeanGL
