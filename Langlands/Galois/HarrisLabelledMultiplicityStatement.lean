import Langlands.Galois.CompatibleFamily
import Langlands.Galois.Local.LabelledHodgeTate
import Mathlib.RepresentationTheory.Semisimple

/-! # Labelled multiplicity removal and completion-valued descent -/

noncomputable section

open scoped TensorProduct

universe uE uL uM uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global

section ScalarExtension

variable {E : Type uE} [Field E]
variable {F : Type uL} [Field F] [TopologicalSpace F]
variable {Ω : Type uM} [Field Ω] [TopologicalSpace Ω]

/-- An actual isomorphism after extension of the coefficient field, with
the same absolute Galois group and its given actions. -/
def IsCoefficientScalarExtension (f : F →+* Ω) (A : Objects.{uE, uL, uV} E F)
    (B : Objects.{uE, uM, uW} E Ω) : Prop :=
  letI : Algebra F Ω := f.toAlgebra
  ∃ e : (Ω ⊗[F] A.val) ≃ₗ[Ω] B.val,
    ∀ (g : Field.absoluteGaloisGroup E) (x : Ω ⊗[F] A.val),
      e (LinearMap.lTensor Ω (A.val.representation g) x) = B.val.representation g (e x)

end ScalarExtension

/-- Taylor's extraction with a Hodge–Tate hypothesis at the chosen label.
The finite extension model retains the labelled twists with multiplicity
one. The all-element characteristic-power identity gives its rational
character, and the good-place comparison keeps track of unramifiedness. -/
def TaylorLabelledMultiplicityRemovalStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] (L : Type uL) [Field L] [NumberField L]
    (lam : FinitePlace L) (A : LambdaAdic.{uE, uL, uV} E L lam)
    (label : E →+* FiniteCompletion L lam) (n m : ℕ)
    (S : Finset (FinitePlace E)) (P : FinitePlace E → Polynomial L) (k : Fin n → ℤ),
    0 < m → Function.Injective k →
    (∀ v ∉ S, (P v).Monic ∧ (P v).natDegree = n) →
    (∀ v ∉ S, residueCharacteristic v ≠ residueCharacteristic lam →
      HasEulerPolynomialAt A v
        (((P v) ^ m).reverse.map (NumberField.FinitePlace.embedding lam))) →
    HasLabelledHodgeTateAt lam A label n m k →
    ∃ (Λ : Type uL) (fieldΛ : Field Λ),
      letI : Field Λ := fieldΛ
      ∃ (algebraΛ : Algebra (FiniteCompletion L lam) Λ)
        (finiteΛ : @FiniteDimensional (FiniteCompletion L lam) Λ _ _ algebraΛ.toModule),
        letI : Algebra (FiniteCompletion L lam) Λ := algebraΛ
        letI : FiniteDimensional (FiniteCompletion L lam) Λ := finiteΛ
        letI : TopologicalSpace Λ := moduleTopology (FiniteCompletion L lam) Λ
        ∃ U : Objects.{uE, uL, uV} E Λ,
          U.val.rank = n ∧ Representation.IsSemisimpleRepresentation U.val.representation ∧
          HasLabelledHodgeTateOver lam U label n 1 k ∧
          (∀ g, (characteristicPolynomial A g).map (algebraMap (FiniteCompletion L lam) Λ) =
            characteristicPolynomial U g ^ m) ∧
          ∀ v ∉ S, residueCharacteristic v ≠ residueCharacteristic lam →
            HasEulerPolynomialAt U v ((P v).reverse.map
              ((algebraMap (FiniteCompletion L lam) Λ).comp
                (NumberField.FinitePlace.embedding lam)))

/-- A semisimple representation with a character in the base completion
and regular Hodge–Tate weights at the indicated label has a model over that
completion. Regularity at the original label is kept in the model. -/
def RegularHodgeTateCoefficientDescentStatement : Prop :=
  ∀ (E : Type uE) [Field E] (L : Type uL) [Field L] [NumberField L]
    (lam : FinitePlace L) (label : E →+* FiniteCompletion L lam)
    (Λ : Type uL) [Field Λ] [Algebra (FiniteCompletion L lam) Λ]
    [FiniteDimensional (FiniteCompletion L lam) Λ],
    letI : TopologicalSpace Λ := moduleTopology (FiniteCompletion L lam) Λ
    ∀ (U : Objects.{uE, uL, uV} E Λ) (n : ℕ) (k : Fin n → ℤ),
      Representation.IsSemisimpleRepresentation U.val.representation →
      (∀ g : Field.absoluteGaloisGroup E,
        ∃ t : FiniteCompletion L lam,
          LinearMap.trace Λ U.val (U.val.representation g) =
            algebraMap (FiniteCompletion L lam) Λ t) →
      Function.Injective k → HasLabelledHodgeTateOver lam U label n 1 k →
      ∃ A : LambdaAdic.{uE, uL, uV} E L lam,
        IsCoefficientScalarExtension (algebraMap (FiniteCompletion L lam) Λ) A U ∧
          HasLabelledHodgeTateAt lam A label n 1 k

end Langlands.GaloisRepresentation
