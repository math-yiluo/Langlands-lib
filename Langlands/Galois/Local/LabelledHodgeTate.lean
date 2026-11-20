import Langlands.Galois.Local.HodgeTate
import Langlands.Global.CompletionPadic

/-! # A single coefficient label for Hodge–Tate decompositions -/

noncomputable section

open scoped TensorProduct

universe uE uL uV

namespace Langlands.GaloisRepresentation

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime] (F : Type uL) [Field F] [TopologicalSpace F]
  [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

instance : UniformContinuousConstSMul F (Closure p F) where
  uniformContinuous_const_smul a := by
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      (uniformContinuous_const_smul (algebraMap F (Closure p F) a) :
        UniformContinuous ((algebraMap F (Closure p F) a) • · : Closure p F → Closure p F))

/-- On the completed algebraic closure the extended Galois action fixes
the whole base field, so it also acts linearly over that field. -/
def galoisLinearOverBase (σ : Field.absoluteGaloisGroup F) : Completed p F →ₗ[F] Completed p F where
  toFun := galoisRingHom p σ
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def,
      UniformSpace.Completion.algebraMap_def, galoisRingHom_coe]
    congr 2
    exact (Closure.galois (p := p) σ).commutes a

/-- At the identity coefficient label, the tensor product over `F` has
twists `k i`, each repeated `m` times, with its actual semilinear action. -/
def HasLabelledHodgeTateDecomposition (A : Objects.{uL, uL, uV} F F)
    (n m : ℕ) (k : Fin n → ℤ) : Prop :=
  ∃ Φ : (Fin n → Fin m → Completed p F) ≃ₗ[Completed p F]
      (Completed p F ⊗[F] A.val),
    ∀ (σ : Field.absoluteGaloisGroup F) (x : Fin n → Fin m → Completed p F),
      Φ (fun i j => cyclotomic p σ ^ k i * galoisRingHom p σ (x i j)) =
        TensorProduct.map (galoisLinearOverBase p F σ) (A.val.representation σ) (Φ x)

end HodgeTate

open Langlands.Global Langlands.Global.CompletionPadic

variable {E : Type uE} [Field E] {L : Type uL} [Field L] [NumberField L]

/-- Labelled comparison for a completion-valued global representation.
The embedding of the global field into the coefficient completion fixes
the label and the map of absolute Galois groups. -/
def HasLabelledHodgeTateAt (lam : FinitePlace L)
    (A : LambdaAdic.{uE, uL, uV} E L lam) (label : E →+* FiniteCompletion L lam)
    (n m : ℕ) (k : Fin n → ℤ) : Prop :=
  letI := padicAlgebra lam
  haveI := padicFinite lam
  HodgeTate.HasLabelledHodgeTateDecomposition (residuePrime lam) (FiniteCompletion L lam)
    (pullback label A) n m k

/-- Labelled comparison after extension of both the local base and the
coefficient field through the specified finite extension. -/
def HasLabelledHodgeTateOver (lam : FinitePlace L)
    {Λ : Type uL} [Field Λ] [TopologicalSpace Λ] [Algebra (FiniteCompletion L lam) Λ]
    [FiniteDimensional (FiniteCompletion L lam) Λ] (A : Objects.{uE, uL, uV} E Λ)
    (label : E →+* FiniteCompletion L lam) (n m : ℕ) (k : Fin n → ℤ) : Prop :=
  letI := padicAlgebra lam
  haveI := padicFinite lam
  letI : Algebra ℚ_[residuePrime lam] Λ :=
    ((algebraMap (FiniteCompletion L lam) Λ).comp (padicMap lam)).toAlgebra
  haveI : IsScalarTower ℚ_[residuePrime lam] (FiniteCompletion L lam) Λ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional ℚ_[residuePrime lam] Λ :=
    FiniteDimensional.trans ℚ_[residuePrime lam] (FiniteCompletion L lam) Λ
  HodgeTate.HasLabelledHodgeTateDecomposition (residuePrime lam) Λ
    (pullback ((algebraMap (FiniteCompletion L lam) Λ).comp label) A) n m k

end Langlands.GaloisRepresentation
