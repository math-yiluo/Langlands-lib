import Langlands.LocalField.Normalization.Definitions
import Mathlib.RingTheory.Norm.Basic

/-! # Relative norms and local absolute-value normalization

These are proposition targets for arbitrary finite extensions of p-adic
fields. The supplied local-field structures are the existing actual structures.
-/

namespace Langlands.LocalClassField

universe u v

/-- Field norms preserve residue-normalized absolute values, while scalar
inclusion raises them to the relative degree. The spectral norm instead
extends the base norm and takes the degree power under the field norm. -/
def RelativeAbsoluteValueLaws : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    (∀ x : E.Carrier,
      TF.normalizedAbs (Algebra.norm F.Carrier x) = TE.normalizedAbs x) ∧
    (∀ x : F.Carrier,
      TE.normalizedAbs (algebraMap F.Carrier E.Carrier x) =
        TF.normalizedAbs x ^ Module.finrank F.Carrier E.Carrier) ∧
    (∀ x : E.Carrier,
      F.canonicalNorm (Algebra.norm F.Carrier x) =
        E.canonicalNorm x ^ Module.finrank F.Carrier E.Carrier) ∧
    (∀ x : F.Carrier,
      E.canonicalNorm (algebraMap F.Carrier E.Carrier x) = F.canonicalNorm x)

/-- Relative order formulas in terms of actual absolute residue degrees and
ramification indices, and the order-zero criterion for norms on units. -/
def RelativeNormOrderLaws : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    (∀ x : E.Carrier,
      (TF.residueDegree : ℤ) * TF.ord (Algebra.norm F.Carrier x) =
        (TE.residueDegree : ℤ) * TE.ord x) ∧
    (∀ x : F.Carrier,
      (TF.ramificationIndex : ℤ) * TE.ord (algebraMap F.Carrier E.Carrier x) =
        (TE.ramificationIndex : ℤ) * TF.ord x) ∧
    (∀ x : E.Carrierˣ,
      TF.ord ((Units.map (Algebra.norm F.Carrier (S := E.Carrier)) x :
        F.Carrierˣ) : F.Carrier) = 0 ↔ TE.ord (x : E.Carrier) = 0)

/-- Relative normalization identities needed for local reciprocity and
transport of the unramified absolute-value character. -/
def RelativeNormCompatibility : Prop :=
  RelativeAbsoluteValueLaws.{u, v} ∧ RelativeNormOrderLaws.{u, v}

end Langlands.LocalClassField
