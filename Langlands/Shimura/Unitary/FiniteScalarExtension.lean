import Langlands.Shimura.Unitary.CMData
import Langlands.Shimura.Unitary.DivisionCondition
import Langlands.Global.Adelic
import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual finite scalar extensions of a CM algebra with involution -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped TensorProduct FiniteExtension

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- CM conjugation, viewed as an involution of the actual commutative algebra. -/
def centerInvolution : AlgebraInvolution E K where
  linear := (cmConjugation E K).toLinearMap
  map_one := map_one (cmConjugation E K)
  map_mul a b := by
    change cmConjugation E K (a * b) = cmConjugation E K b * cmConjugation E K a
    rw [map_mul, mul_comm]
  involutive := cmConjugation_involutive E K

/-- The completed quadratic etale center at an actual finite place of `E`. -/
abbrev LocalCenter (v : Langlands.Global.FinitePlace E) := FiniteCompletion E v ⊗[E] K

/-- The induced conjugation fixes `E_v` and acts on the actual CM factor. -/
def localConjugation (v : Langlands.Global.FinitePlace E) :
    AlgebraInvolution (FiniteCompletion E v) (LocalCenter E K v) :=
  (centerInvolution E K).baseChange (FiniteCompletion E v)

@[simp] theorem localConjugation_tmul (v : Langlands.Global.FinitePlace E)
    (s : FiniteCompletion E v) (k : K) :
    localConjugation E K v (s ⊗ₜ[E] k) = s ⊗ₜ[E] cmConjugation E K k := rfl

variable (A : Type w) [Ring A] [Algebra E A] [Algebra K A]
  [IsScalarTower E K A]

/-- The actual local algebra over the completed totally real field. -/
abbrev LocalAlgebra (v : Langlands.Global.FinitePlace E) := FiniteCompletion E v ⊗[E] A

/-- The actual algebra at a finite place of the CM center. -/
abbrev CompletedAlgebra (w : Langlands.Global.FinitePlace K) := FiniteCompletion K w ⊗[K] A

/-- The embedded completed quadratic center, with its specified scalar map. -/
def localCenterMap (v : Langlands.Global.FinitePlace E) :
    LocalCenter E K v →ₐ[FiniteCompletion E v] LocalAlgebra E A v :=
  Algebra.TensorProduct.map (AlgHom.id (FiniteCompletion E v) (FiniteCompletion E v))
    (IsScalarTower.toAlgHom E K A)

@[simp] theorem localCenterMap_tmul (v : Langlands.Global.FinitePlace E)
    (s : FiniteCompletion E v) (k : K) :
    localCenterMap E K A v (s ⊗ₜ[E] k) = s ⊗ₜ[E] algebraMap K A k := rfl

@[simp] theorem localCenterMap_scalar (v : Langlands.Global.FinitePlace E) (s : FiniteCompletion E v) :
    localCenterMap E K A v (algebraMap (FiniteCompletion E v) (LocalCenter E K v) s) =
      algebraMap (FiniteCompletion E v) (LocalAlgebra E A v) s :=
  (localCenterMap E K A v).commutes s

variable {E K A}

/-- The induced involution on `E_v tensor_E A`. -/
def localInvolution (σ : SecondKindInvolution E K A) (v : Langlands.Global.FinitePlace E) :
    AlgebraInvolution (FiniteCompletion E v) (LocalAlgebra E A v) :=
  σ.involution.baseChange (FiniteCompletion E v)

@[simp] theorem localInvolution_tmul (σ : SecondKindInvolution E K A)
    (v : Langlands.Global.FinitePlace E) (s : FiniteCompletion E v) (a : A) :
    localInvolution σ v (s ⊗ₜ[E] a) = s ⊗ₜ[E] σ.involution a := rfl

/-- The local involution induces the actual conjugation on the completed center. -/
theorem localInvolution_center (σ : SecondKindInvolution E K A)
    (v : Langlands.Global.FinitePlace E) (z : LocalCenter E K v) :
    localInvolution σ v (localCenterMap E K A v z) =
      localCenterMap E K A v (localConjugation E K v z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s k => simp [σ.onCenter]

variable (E K A)
variable (v : Langlands.Global.FinitePlace E) (w : Langlands.Global.FinitePlace K) [w.asIdeal.LiesOver v.asIdeal]

/-- Evaluation of the completed quadratic center at the actual place `w` above `v`. -/
def completedCenterMap : LocalCenter E K v →ₐ[FiniteCompletion E v] FiniteCompletion K w :=
  Algebra.TensorProduct.lift (Algebra.ofId (FiniteCompletion E v) (FiniteCompletion K w))
    (IsScalarTower.toAlgHom E K (FiniteCompletion K w)) (fun _ _ => .all _ _)

@[simp] theorem completedCenterMap_tmul (s : FiniteCompletion E v) (k : K) :
    completedCenterMap E K v w (s ⊗ₜ[E] k) =
      FiniteExtension.completionMap v w s * algebraMap K (FiniteCompletion K w) k := rfl

/-- The actual comparison from `E_v tensor_E A` to `K_w tensor_K A`. -/
def toCompletedAlgebra :
    LocalAlgebra E A v →ₐ[FiniteCompletion E v] CompletedAlgebra K A w :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (FiniteCompletion E v) (CompletedAlgebra K A w))
    ((Algebra.TensorProduct.includeRight : A →ₐ[K] CompletedAlgebra K A w).restrictScalars E)
    (fun s a => Algebra.commutes s _)

@[simp] theorem toCompletedAlgebra_tmul (s : FiniteCompletion E v) (a : A) :
    toCompletedAlgebra E K A v w (s ⊗ₜ[E] a) =
      (FiniteExtension.completionMap v w s) ⊗ₜ[K] a := by
  change ((FiniteExtension.completionMap v w s) ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] a) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The two actual scalar maps agree on the entire completed quadratic center. -/
theorem toCompletedAlgebra_center (z : LocalCenter E K v) :
    toCompletedAlgebra E K A v w (localCenterMap E K A v z) =
      algebraMap (FiniteCompletion K w) (CompletedAlgebra K A w)
        (completedCenterMap E K v w z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s k =>
    rw [localCenterMap_tmul, toCompletedAlgebra_tmul, completedCenterMap_tmul]
    change _ = _ ⊗ₜ[K] (1 : A)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
    congr 1
    simp [Algebra.smul_def, mul_comm]

/-- Local division is invertibility of every nonzero element of the actual algebra. -/
def IsDivisionAt : Prop :=
  ∀ a : CompletedAlgebra K A w, a ≠ 0 → IsUnit a

/-- Local splitting is an actual equivalence over the completed CM center. -/
def IsSplitAt (n : ℕ) : Prop :=
  Nonempty (CompletedAlgebra K A w ≃ₐ[FiniteCompletion K w]
    Matrix (Fin n) (Fin n) (FiniteCompletion K w))

/-- The scalar-extension inclusion is injective, by flatness over the field `K`. -/
theorem completedInclude_injective :
    Function.Injective (Algebra.TensorProduct.includeRight :
      A →ₐ[K] CompletedAlgebra K A w) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K (FiniteCompletion K w)).injective

variable {E K A v w}

/-- Reflection of division uses both the injective tensor inclusion and the
finite-dimensional multiplication endomorphism on the original algebra. -/
theorem isDivision_of_isDivisionAt {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (w : Langlands.Global.FinitePlace K) (h : IsDivisionAt K A w) : D.IsDivision := by
  letI : FiniteDimensional K A := D.finite
  let f : A →ₐ[K] CompletedAlgebra K A w := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := completedInclude_injective K A w
  intro a ha
  have hfa : IsUnit (f a) := h (f a) (fun hz => ha (hf (hz.trans (map_zero f).symm)))
  have hi : Function.Injective (LinearMap.mulLeft K a) := by
    intro x y hxy
    apply hf
    apply hfa.mul_right_injective
    change a * x = a * y at hxy
    simpa only [← map_mul] using congrArg f hxy
  exact IsUnit.isUnit_iff_mulLeft_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

end Langlands.Shimura.FiniteUnitary
