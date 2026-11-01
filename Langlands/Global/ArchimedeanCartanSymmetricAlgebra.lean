import Langlands.Global.ArchimedeanRelativeAdjoint
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! # Actual Cartan symmetric algebras and compact conjugation -/

noncomputable section
universe u
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Complex scalar extension of the actual self-adjoint Cartan complement. -/
abbrev ComplexCartanComplement := ℂ ⊗[ℝ] (cartanComplement K n)

/-- The actual complementary inclusion after scalar extension. -/
def cartanComplexInclusion : ComplexCartanComplement K n →ₗ[ℂ] ComplexLieAlgebra K n :=
  (cartanComplement K n).subtype.baseChange ℂ

/-- The actual complementary projection after scalar extension. -/
def cartanComplexProjection : ComplexLieAlgebra K n →ₗ[ℂ] ComplexCartanComplement K n :=
  (cartanComplementProjection K n).baseChange ℂ

@[simp]
theorem cartanComplexInclusion_tmul (z : ℂ) (X : cartanComplement K n) :
    cartanComplexInclusion K n (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] (X : RealLieAlgebra K n) := rfl

@[simp]
theorem cartanComplexProjection_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    cartanComplexProjection K n (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] cartanComplementProjection K n X := rfl

@[simp]
theorem cartanComplexProjection_inclusion (X : ComplexCartanComplement K n) :
    cartanComplexProjection K n (cartanComplexInclusion K n X) = X := by
  have hreal (Y : cartanComplement K n) :
      cartanComplementProjection K n Y = Y := by
    apply Subtype.ext
    change (2 : ℝ)⁻¹ • ((Y : RealLieAlgebra K n) + star (Y : RealLieAlgebra K n)) = Y
    rw [(mem_cartanComplement K n Y).mp Y.property]
    module
  induction X using TensorProduct.inductionOn with
  | tmul z Y => simp [hreal]
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem cartanComplexInclusion_injective : Function.Injective (cartanComplexInclusion K n) :=
  Function.LeftInverse.injective (cartanComplexProjection_inclusion K n)

theorem realLieConjugation_mem_cartanComplement (k : standardInfiniteCompact K n)
    (X : cartanComplement K n) :
    realLieConjugation K n k.val X ∈ cartanComplement K n := by
  rw [mem_cartanComplement, ← realLieConjugation_star]
  rw [(mem_cartanComplement K n X).mp X.property]

/-- The full standard compact group acts on the self-adjoint real complement. -/
def cartanRealConjugation (k : standardInfiniteCompact K n) :
    cartanComplement K n ≃ₗ[ℝ] cartanComplement K n where
  toFun X := ⟨realLieConjugation K n k.val X,
    realLieConjugation_mem_cartanComplement K n k X⟩
  invFun X := ⟨realLieConjugation K n k⁻¹.val X,
    realLieConjugation_mem_cartanComplement K n k⁻¹ X⟩
  left_inv X := Subtype.ext (by simp)
  right_inv X := Subtype.ext (by simp)
  map_add' X Y := Subtype.ext (map_add (realLieConjugation K n k.val) X.val Y.val)
  map_smul' r X := Subtype.ext (map_smul (realLieConjugation K n k.val) r X.val)

@[simp]
theorem cartanRealConjugation_coe (k : standardInfiniteCompact K n)
    (X : cartanComplement K n) :
    (cartanRealConjugation K n k X : RealLieAlgebra K n) =
      realLieConjugation K n k.val X := rfl

@[simp]
theorem cartanRealConjugation_one :
    cartanRealConjugation K n 1 = LinearEquiv.refl ℝ _ := by
  ext X
  simp

theorem cartanRealConjugation_mul (k l : standardInfiniteCompact K n) :
    cartanRealConjugation K n (k * l) =
      (cartanRealConjugation K n l).trans (cartanRealConjugation K n k) := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  exact congrArg (fun e => e (X : RealLieAlgebra K n))
    (realLieConjugation_mul K n k.val l.val)

@[simp]
theorem cartanRealConjugation_inv (k : standardInfiniteCompact K n) :
    cartanRealConjugation K n k⁻¹ = (cartanRealConjugation K n k).symm := by
  apply LinearEquiv.ext
  intro X
  rfl

theorem cartanComplementProjection_conjugation (k : standardInfiniteCompact K n)
    (X : RealLieAlgebra K n) :
    cartanComplementProjection K n (realLieConjugation K n k.val X) =
      cartanRealConjugation K n k (cartanComplementProjection K n X) := by
  apply Subtype.ext
  simp only [cartanComplementProjection_apply, cartanRealConjugation_coe,
    map_smul, map_add, realLieConjugation_star]

/-- Complex scalar extension of actual compact conjugation on the complement. -/
def cartanComplexConjugation (k : standardInfiniteCompact K n) :
    ComplexCartanComplement K n ≃ₗ[ℂ] ComplexCartanComplement K n :=
  (cartanRealConjugation K n k).baseChange ℝ ℂ _ _

@[simp]
theorem cartanComplexConjugation_tmul (k : standardInfiniteCompact K n)
    (z : ℂ) (X : cartanComplement K n) :
    cartanComplexConjugation K n k (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] cartanRealConjugation K n k X := rfl

theorem cartanComplexInclusion_conjugation (k : standardInfiniteCompact K n)
    (X : ComplexCartanComplement K n) :
    cartanComplexInclusion K n (cartanComplexConjugation K n k X) =
      complexLieConjugation K n k.val (cartanComplexInclusion K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => rfl
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem cartanComplexProjection_conjugation (k : standardInfiniteCompact K n)
    (X : ComplexLieAlgebra K n) :
    cartanComplexProjection K n (complexLieConjugation K n k.val X) =
      cartanComplexConjugation K n k (cartanComplexProjection K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp only [complexLieConjugation_tmul, cartanComplexProjection_tmul,
      cartanComplexConjugation_tmul, cartanComplementProjection_conjugation]
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp]
theorem cartanComplexConjugation_one :
    cartanComplexConjugation K n 1 = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro X
  apply cartanComplexInclusion_injective K n
  simp [cartanComplexInclusion_conjugation]

theorem cartanComplexConjugation_mul (k l : standardInfiniteCompact K n) :
    cartanComplexConjugation K n (k * l) =
      (cartanComplexConjugation K n l).trans (cartanComplexConjugation K n k) := by
  apply LinearEquiv.ext
  intro X
  apply cartanComplexInclusion_injective K n
  simp only [cartanComplexInclusion_conjugation, LinearEquiv.trans_apply,
    Subgroup.coe_mul, complexLieConjugation_mul, LieEquiv.trans_apply]

@[simp]
theorem cartanComplexConjugation_inv (k : standardInfiniteCompact K n) :
    cartanComplexConjugation K n k⁻¹ = (cartanComplexConjugation K n k).symm := by
  apply LinearEquiv.ext
  intro X
  apply (cartanComplexConjugation K n k).injective
  have h := congrArg (fun e : ComplexCartanComplement K n ≃ₗ[ℂ]
    ComplexCartanComplement K n => e X) (cartanComplexConjugation_mul K n k k⁻¹)
  simpa using h.symm

/-- The symmetric algebra of the entire actual complexified matrix Lie algebra. -/
abbrev LieSymmetricAlgebra := SymmetricAlgebra ℂ (ComplexLieAlgebra K n)

/-- The symmetric algebra of the actual complexified Cartan complement. -/
abbrev CartanSymmetricAlgebra := SymmetricAlgebra ℂ (ComplexCartanComplement K n)

/-- The symmetric-algebra lift of the actual complementary inclusion. -/
def cartanSymmetricInclusion : CartanSymmetricAlgebra K n →ₐ[ℂ] LieSymmetricAlgebra K n :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ (ComplexLieAlgebra K n)).comp
    (cartanComplexInclusion K n))

/-- The symmetric-algebra lift of the actual complementary projection. -/
def cartanSymmetricProjection : LieSymmetricAlgebra K n →ₐ[ℂ] CartanSymmetricAlgebra K n :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ (ComplexCartanComplement K n)).comp
    (cartanComplexProjection K n))

@[simp]
theorem cartanSymmetricInclusion_ι (X : ComplexCartanComplement K n) :
    cartanSymmetricInclusion K n (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (cartanComplexInclusion K n X) :=
  SymmetricAlgebra.lift_ι_apply _ _

@[simp]
theorem cartanSymmetricProjection_ι (X : ComplexLieAlgebra K n) :
    cartanSymmetricProjection K n (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (cartanComplexProjection K n X) :=
  SymmetricAlgebra.lift_ι_apply _ _

@[simp]
theorem cartanSymmetricProjection_inclusion (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricProjection K n (cartanSymmetricInclusion K n P) = P := by
  have h : (cartanSymmetricProjection K n).comp (cartanSymmetricInclusion K n) =
      AlgHom.id ℂ (CartanSymmetricAlgebra K n) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    simp
  exact AlgHom.congr_fun h P

theorem cartanSymmetricInclusion_injective : Function.Injective (cartanSymmetricInclusion K n) :=
  Function.LeftInverse.injective (cartanSymmetricProjection_inclusion K n)

theorem cartanSymmetricProjection_surjective : Function.Surjective (cartanSymmetricProjection K n) :=
  Function.RightInverse.surjective (cartanSymmetricProjection_inclusion K n)

private def symmetricEquiv {V : Type u} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] V) : SymmetricAlgebra ℂ V ≃ₐ[ℂ] SymmetricAlgebra ℂ V :=
  { SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.toLinearMap) with
    invFun := SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.symm.toLinearMap)
    left_inv := by
      have h :
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.symm.toLinearMap)).comp
            (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.toLinearMap)) =
          AlgHom.id ℂ (SymmetricAlgebra ℂ V) := by
        apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro X
        simp
      exact fun P => AlgHom.congr_fun h P
    right_inv := by
      have h :
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.toLinearMap)).comp
            (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ V).comp e.symm.toLinearMap)) =
          AlgHom.id ℂ (SymmetricAlgebra ℂ V) := by
        apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro X
        simp
      exact fun P => AlgHom.congr_fun h P }

private theorem symmetricEquiv_ι {V : Type u} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] V) (X : V) :
    symmetricEquiv e (SymmetricAlgebra.ι ℂ V X) = SymmetricAlgebra.ι ℂ V (e X) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Actual full-group adjoint conjugation extended to the symmetric algebra. -/
def lieSymmetricConjugation (g : InfiniteAdelicGL K n) :
    LieSymmetricAlgebra K n ≃ₐ[ℂ] LieSymmetricAlgebra K n :=
  symmetricEquiv (complexLieConjugation K n g).toLinearEquiv

@[simp]
theorem lieSymmetricConjugation_ι (g : InfiniteAdelicGL K n)
    (X : ComplexLieAlgebra K n) :
    lieSymmetricConjugation K n g (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (complexLieConjugation K n g X) :=
  symmetricEquiv_ι _ _

@[simp]
theorem lieSymmetricConjugation_one :
    lieSymmetricConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro X
  simp

theorem lieSymmetricConjugation_mul (g h : InfiniteAdelicGL K n) :
    lieSymmetricConjugation K n (g * h) =
      (lieSymmetricConjugation K n h).trans (lieSymmetricConjugation K n g) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro X
  simp [complexLieConjugation_mul]

@[simp]
theorem lieSymmetricConjugation_inv (g : InfiniteAdelicGL K n) :
    lieSymmetricConjugation K n g⁻¹ = (lieSymmetricConjugation K n g).symm := by
  apply AlgEquiv.ext
  intro P
  apply (lieSymmetricConjugation K n g).injective
  have h := congrArg (fun e : LieSymmetricAlgebra K n ≃ₐ[ℂ]
    LieSymmetricAlgebra K n => e P) (lieSymmetricConjugation_mul K n g g⁻¹)
  simpa using h.symm

/-- Actual compact conjugation on the complementary symmetric algebra. -/
def cartanSymmetricConjugation (k : standardInfiniteCompact K n) :
    CartanSymmetricAlgebra K n ≃ₐ[ℂ] CartanSymmetricAlgebra K n :=
  symmetricEquiv (cartanComplexConjugation K n k)

@[simp]
theorem cartanSymmetricConjugation_ι (k : standardInfiniteCompact K n)
    (X : ComplexCartanComplement K n) :
    cartanSymmetricConjugation K n k (SymmetricAlgebra.ι ℂ _ X) =
      SymmetricAlgebra.ι ℂ _ (cartanComplexConjugation K n k X) :=
  symmetricEquiv_ι _ _

@[simp]
theorem cartanSymmetricConjugation_one :
    cartanSymmetricConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro X
  simp

theorem cartanSymmetricConjugation_mul (k l : standardInfiniteCompact K n) :
    cartanSymmetricConjugation K n (k * l) =
      (cartanSymmetricConjugation K n l).trans (cartanSymmetricConjugation K n k) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro X
  simp [cartanComplexConjugation_mul]

@[simp]
theorem cartanSymmetricConjugation_inv (k : standardInfiniteCompact K n) :
    cartanSymmetricConjugation K n k⁻¹ = (cartanSymmetricConjugation K n k).symm := by
  apply AlgEquiv.ext
  intro P
  apply (cartanSymmetricConjugation K n k).injective
  have h := congrArg (fun e : CartanSymmetricAlgebra K n ≃ₐ[ℂ]
    CartanSymmetricAlgebra K n => e P) (cartanSymmetricConjugation_mul K n k k⁻¹)
  simpa using h.symm

theorem cartanSymmetricInclusion_conjugation (k : standardInfiniteCompact K n)
    (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricInclusion K n (cartanSymmetricConjugation K n k P) =
      lieSymmetricConjugation K n k.val (cartanSymmetricInclusion K n P) := by
  have h : (cartanSymmetricInclusion K n).comp
        (cartanSymmetricConjugation K n k).toAlgHom =
      (lieSymmetricConjugation K n k.val).toAlgHom.comp
        (cartanSymmetricInclusion K n) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    simp [cartanComplexInclusion_conjugation]
  exact AlgHom.congr_fun h P

theorem cartanSymmetricProjection_conjugation (k : standardInfiniteCompact K n)
    (P : LieSymmetricAlgebra K n) :
    cartanSymmetricProjection K n (lieSymmetricConjugation K n k.val P) =
      cartanSymmetricConjugation K n k (cartanSymmetricProjection K n P) := by
  have h : (cartanSymmetricProjection K n).comp
        (lieSymmetricConjugation K n k.val).toAlgHom =
      (cartanSymmetricConjugation K n k).toAlgHom.comp
        (cartanSymmetricProjection K n) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro X
    simp [cartanComplexProjection_conjugation]
  exact AlgHom.congr_fun h P

section Noetherian

variable [NumberField K]

local instance cartanSymmetric_realLieAlgebra_finiteDimensional :
    FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

/-- Finite actual matrix dimension gives a Noetherian complementary symmetric algebra. -/
instance cartanSymmetricAlgebra_isNoetherianRing : IsNoetherianRing (CartanSymmetricAlgebra K n) := by
  let b := Module.finBasis ℂ (ComplexCartanComplement K n)
  exact isNoetherianRing_of_ringEquiv _ (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv

end Noetherian

end Langlands.Global.ArchimedeanGL
