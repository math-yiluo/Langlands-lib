import Langlands.ClassFieldTheory.Local.Units
import Mathlib.Topology.Compactness.Compact

/-!
# Topology and compact lifting for actual local-field unit filtrations

These proposition definitions use the published reduction-kernel filtration.
The lifting criterion is conditional on preservation and approximation at each
successive level; it makes no arithmetic assertion about the field norm.
-/

namespace Langlands.LocalClassField

universe u v

/-- The actual unit filtration is compact, closed, decreasing and separated,
and its zeroth level is the valuation-unit subgroup, for every supplied topology. -/
def UnitFiltrationStructuralLaws : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    (∀ n : ℕ, IsCompact (T.unitFiltration n : Set F.Carrierˣ) ∧
      IsClosed (T.unitFiltration n : Set F.Carrierˣ)) ∧
    Antitone T.unitFiltration ∧
    (∀ x : F.Carrierˣ, (∀ n : ℕ, x ∈ T.unitFiltration n) → x = 1) ∧
    T.unitFiltration 0 = T.unitSubgroup

/-- A continuous homomorphism preserving actual unit filtrations and admitting
one-level approximations maps every filtration subgroup onto its counterpart.
No extension structure between the two fields is required. -/
def UnitFiltrationCompactLifting : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    ∀ f : E.Carrierˣ →ₜ* F.Carrierˣ,
      (∀ (n : ℕ) (x : E.Carrierˣ),
        x ∈ S.unitFiltration n → f x ∈ T.unitFiltration n) →
      (∀ (n : ℕ) (y : F.Carrierˣ), y ∈ T.unitFiltration n →
        ∃ x : E.Carrierˣ, x ∈ S.unitFiltration n ∧
          y * (f x)⁻¹ ∈ T.unitFiltration (n + 1)) →
      ∀ n : ℕ, (S.unitFiltration n).map f.toMonoidHom = T.unitFiltration n

/-- The complete topological prerequisite, with structural laws in both
independent carrier universes and the compact lifting criterion between them. -/
def UnitFiltrationTopologyTheorems : Prop :=
  UnitFiltrationStructuralLaws.{u} ∧
    UnitFiltrationStructuralLaws.{v} ∧
      UnitFiltrationCompactLifting.{u, v}

end Langlands.LocalClassField
