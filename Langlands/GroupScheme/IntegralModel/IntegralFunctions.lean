import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Integral functions on the generic fibre and their finite generation

For a commutative `R`-algebra `A` and an `R`-algebra `K`, an element `f` of
`K ⊗[R] A` is an *integral function* when its value at every `R`-point of `A`
lies in the image of `R`. These elements form an `R`-subalgebra of
`K ⊗[R] A`. For an affine flat finite-type group scheme `Spec A` over a Henselian
discrete valuation ring `R` with algebraically closed residue field and smooth
generic fibre, this subalgebra is the coordinate ring of the Néron–Kaletha–Prasad
smoothening. The statement below asserts that it is a finitely generated
`R`-algebra (KP Theorem A.6.2, Bruhat–Tits II 1.7.3 f). -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel

variable (R : Type u) (K : Type v) (A : Type w) [CommRing R] [CommRing K]
  [Algebra R K] [CommRing A] [Algebra R A]

/-- The value in `K` at an `R`-point `φ` of `A` of a function on the generic
fibre: the `K`-algebra map `K ⊗[R] A → K` sending `c ⊗ a` to `c * φ a`. -/
def genericEval (φ : A →ₐ[R] R) : K ⊗[R] A →ₐ[K] K :=
  Algebra.TensorProduct.lift (Algebra.ofId K K) ((Algebra.ofId R K).comp φ)
    fun _ _ => .all _ _

@[simp]
theorem genericEval_tmul (φ : A →ₐ[R] R) (c : K) (a : A) :
    genericEval R K A φ (c ⊗ₜ a) = c * algebraMap R K (φ a) := by
  simp [genericEval]

/-- The `R`-integral functions on the generic fibre: elements of `K ⊗[R] A`
whose value at every `R`-point of `A` lies in the image of `R`. -/
def integralFunctions : Subalgebra R (K ⊗[R] A) :=
  ⨅ φ : A →ₐ[R] R, (⊥ : Subalgebra R K).comap ((genericEval R K A φ).restrictScalars R)

theorem mem_integralFunctions {f : K ⊗[R] A} :
    f ∈ integralFunctions R K A ↔
      ∀ φ : A →ₐ[R] R, genericEval R K A φ f ∈ Set.range (algebraMap R K) := by
  simp only [integralFunctions, Algebra.mem_iInf, Subalgebra.mem_comap,
    AlgHom.coe_restrictScalars', Algebra.mem_bot]

/-- Finite generation of the integral functions (KP Theorem A.6.2, Bruhat–Tits
II 1.7.3 f): for a flat finitely generated commutative Hopf algebra `A` over a
Henselian discrete valuation ring `R` with algebraically closed residue field,
whose generic fibre `K ⊗[R] A` is smooth over the fraction field `K`, the
`R`-algebra of integral functions on the generic fibre is finitely generated. -/
def IntegralFunctionsFiniteTypeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : Type u) [CommRing A] [HopfAlgebra R A] [Module.Flat R A]
    [Algebra.FiniteType R A],
    Algebra.Smooth K (K ⊗[R] A) →
    Algebra.FiniteType R (integralFunctions R K A)

end Langlands.GroupScheme.IntegralModel
