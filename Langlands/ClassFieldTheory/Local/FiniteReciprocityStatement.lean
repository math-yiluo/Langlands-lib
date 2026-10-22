import Langlands.LocalField.Normalization.Definitions
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # Finite abelian local reciprocity

These are proposition definitions on actual field-norm quotients and Galois
groups. No reciprocity map or existence theorem is supplied as an assumption.
-/

namespace Langlands.LocalClassField

universe u v w

/-- Finite local reciprocity with geometric Frobenius normalization and the
valuation-unit/inertia correspondence, expressed through the actual valuation.
The action congruences take place in the extension field itself. -/
def FiniteAbelianReciprocity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    letI := TF.topology
    ∃ r : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range)
        ≃ₜ* Gal(E.Carrier/F.Carrier),
      (∀ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 1 →
        ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
          TE.discreteValuation
            ((r (QuotientGroup.mk a)).symm x - x ^ TF.residueCardinality) < 1) ∧
      (∀ σ : Gal(E.Carrier/F.Carrier),
        (∃ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 0 ∧
          r (QuotientGroup.mk a) = σ) ↔
        ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
          TE.discreteValuation (σ x - x) < 1)

/-- In a finite abelian tower, norm corresponds to Galois inclusion and scalar
inclusion corresponds to transfer. For an abelian ambient Galois group the
included transfer is the degree power map. -/
def FiniteAbelianNormTransfer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p) (L : PadicField.{w} p)
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier]
    [Algebra E.Carrier L.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsScalarTower (Padic p) E.Carrier L.Carrier]
    [IsScalarTower F.Carrier E.Carrier L.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier L.Carrier]
    [FiniteDimensional E.Carrier L.Carrier]
    [IsAbelianGalois F.Carrier L.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    letI := TF.topology
    letI := TE.topology
    ∃ rF : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := L.Carrier))).range)
        ≃ₜ* Gal(L.Carrier/F.Carrier),
      ∃ rE : (E.Carrierˣ ⧸ (Units.map (Algebra.norm E.Carrier (S := L.Carrier))).range)
          ≃ₜ* Gal(L.Carrier/E.Carrier),
        (∀ a : E.Carrierˣ,
          rF (QuotientGroup.mk (Units.map (Algebra.norm F.Carrier (S := E.Carrier)) a)) =
            (rE (QuotientGroup.mk a)).restrictScalars F.Carrier) ∧
        (∀ a : F.Carrierˣ,
          (rE (QuotientGroup.mk
            (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a))).restrictScalars
                F.Carrier =
            rF (QuotientGroup.mk a) ^ Module.finrank F.Carrier E.Carrier)

/-- Reciprocity quotients can be chosen compatibly with restriction in a finite
abelian tower over a fixed base field. -/
def FiniteAbelianRestriction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p) (L : PadicField.{w} p)
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier]
    [Algebra E.Carrier L.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsScalarTower (Padic p) E.Carrier L.Carrier]
    [IsScalarTower F.Carrier E.Carrier L.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier L.Carrier]
    [IsAbelianGalois F.Carrier L.Carrier]
    (TF : F.TopologicalData),
    letI := TF.topology
    letI := IsAbelianGalois.tower_bot F.Carrier E.Carrier L.Carrier
    ∃ rE : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range)
        ≃ₜ* Gal(E.Carrier/F.Carrier),
      ∃ rL : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := L.Carrier))).range)
          ≃ₜ* Gal(L.Carrier/F.Carrier),
        ∀ a : F.Carrierˣ,
          AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := L.Carrier) E.Carrier
              (rL (QuotientGroup.mk a)) =
            rE (QuotientGroup.mk a)

/-- Finite abelian existence, normalization, inertia and tower diagrams.
Global coherent-system existence and uniqueness are separate targets. -/
def FiniteAbelianReciprocityTheorems : Prop :=
  FiniteAbelianReciprocity.{u, v} ∧
    FiniteAbelianNormTransfer.{u, v, w} ∧
    FiniteAbelianRestriction.{u, v, w}

end Langlands.LocalClassField
