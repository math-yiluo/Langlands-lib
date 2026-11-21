import Langlands.Galois.Local.LabelledHodgeTate
import Langlands.Galois.CyclotomicTwist
import Langlands.Galois.HeckeCharacterRealization
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Coefficient-labelled Hodge–Tate grades and an actual character shift -/

noncomputable section
set_option autoImplicit false

universe u uE uV

open scoped TensorProduct

namespace Langlands.GaloisRepresentation.HodgeTate

variable (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [TopologicalSpace F]
  [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- The actual grade at exponent `j` at the identity coefficient label.
This is a subspace over `F`, not over its completed algebraic closure. -/
def labelledGrade (B : Objects.{u, u, uV} F F) (j : ℤ) :
    Submodule F (Completed p F ⊗[F] B.val) where
  carrier := {x | ∀ g : Field.absoluteGaloisGroup F,
    TensorProduct.map (galoisLinearOverBase p F g) (B.val.representation g) x =
      cyclotomic p g ^ j • x}
  zero_mem' g := by simp
  add_mem' hx hy g := by rw [map_add, hx g, hy g, smul_add]
  smul_mem' a x hx g := by
    rw [map_smul, hx g, smul_comm]

/-- The canonical comparison multiplies each actual graded period by a
coefficient in the completed algebraic closure. -/
def labelledGradeComparison (B : Objects.{u, u, uV} F F) (j : ℤ) :
    (Completed p F ⊗[F] labelledGrade p F B j) →ₗ[Completed p F]
      (Completed p F ⊗[F] B.val) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • (labelledGrade p F B j).subtype
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => mul_smul a b _ }

/-- Period comparison and finite-dimensional grade ranks for the same
representation imply the labelled decomposition. The map can use just the
listed grades; no other grade is needed for its bijectivity. -/
def HarrisLabelledHTFromGradesStatement : Prop :=
  ∀ (B : Objects.{u, u, uV} F F) (n a : ℕ) (k : Fin n → ℤ),
    Function.Injective k →
    (∀ i, Module.Finite F (labelledGrade p F B (k i))) →
    (∀ i, Module.finrank F (labelledGrade p F B (k i)) = a) →
    Function.Bijective (fun x : (i : Fin n) →
      Completed p F ⊗[F] labelledGrade p F B (k i) =>
      ∑ i, labelledGradeComparison p F B (k i) (x i)) →
    HasLabelledHodgeTateDecomposition p F B n a k

end Langlands.GaloisRepresentation.HodgeTate

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.CompletionPadic

section Character

variable (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [TopologicalSpace F]
  [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- Nonzero period for the given local scalar action. -/
def HasLocalCharacterTateExponent (χ : Field.absoluteGaloisGroup F →* Fˣ) (t : ℤ) : Prop :=
  ∃ x : HodgeTate.Completed p F, x ≠ 0 ∧
    ∀ g : Field.absoluteGaloisGroup F,
      algebraMap F (HodgeTate.Completed p F) (χ g : F) * HodgeTate.galoisRingHom p g x =
        HodgeTate.cyclotomic p g ^ t * x

end Character

set_option maxHeartbeats 1600000 in
/-- Rank-one Tate exponent at the label of a completion-valued character:
a nonzero period for its actual local pullback. -/
def HasCharacterTateExponentAt {E : Type uE} [Field E] {L : Type u} [Field L] [NumberField L]
    (lam : FinitePlace L) (label : E →+* FiniteCompletion L lam)
    (χ : LambdaAdicCharacter E L lam) (t : ℤ) : Prop :=
  letI := padicAlgebra lam
  haveI := padicFinite lam
  HasLocalCharacterTateExponent (residuePrime lam) (FiniteCompletion L lam)
    (χ.toMonoidHom.comp (Field.absoluteGaloisGroup.map label).toMonoidHom) t

/-- The inverse twist by an actual rank-one avatar subtracts its Tate
exponent at the same label, preserving all multiplicities. -/
def HarrisLabelledInverseTwistStatement : Prop :=
  ∀ (E : Type uE) (L : Type u) [Field E] [Field L] [NumberField L] (lam : FinitePlace L)
    (M : LambdaAdic.{uE, u, uV} E L lam) (label : E →+* FiniteCompletion L lam)
    (χ : LambdaAdicCharacter E L lam) (n a : ℕ) (k : Fin n → ℤ) (t : ℤ),
    HasLabelledHodgeTateAt lam M label n a k → HasCharacterTateExponentAt lam label χ t →
    HasLabelledHodgeTateAt lam
      (twist χ.toMonoidHom⁻¹ (Units.continuous_val.comp χ.continuous.inv) M)
      label n a (fun i => k i - t)

/-- The two local linear-algebra steps after the coefficient and character comparisons. -/
def HarrisLabelledGradeAndTwistStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [TopologicalSpace F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F],
    HodgeTate.HarrisLabelledHTFromGradesStatement.{u, uV} p F) ∧
    HarrisLabelledInverseTwistStatement.{u, uE, uV}

end Langlands.GaloisRepresentation
