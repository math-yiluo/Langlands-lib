import Langlands.ClassFieldTheory.Local.FiniteArtin
import Langlands.LocalField.Normalization.Definitions

/-!
# Coherent geometric finite Artin systems

These proposition definitions state the normalized finite-family relation and
its unconditional existence and uniqueness. They provide theorem targets,
not an arithmetic proof or a reconstruction of profinite reciprocity.
-/

namespace Langlands.LocalClassField

universe u

/-- The actual finite norm-residue system with geometric residue normalization.
The inverse of the automorphism attached to a uniformizer induces the
residue-cardinality power map on every finite abelian residue extension. -/
def GeometricFiniteArtinSystemRelation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) :
    letI := T.topology
    FiniteArtinFamily F.Carrier → Prop :=
  letI := T.topology
  fun a =>
    FiniteArtinSystemRelation a ∧
      ∀ (L : LocalFiniteAbelianExtension F)
        (S : (L.asPadicField (p := p)).TopologicalData)
        (b : F.Carrierˣ), T.ord (b : F.Carrier) = 1 →
        ∀ x : L.field, S.discreteValuation x ≤ 1 →
          S.discreteValuation
            ((a L b).symm x - x ^ T.residueCardinality) < 1

/-- For every p-adic field and supplied original topological datum, exactly
one continuous finite Artin family has the entire geometric system relation.
No candidate map or arithmetic certificate is assumed. -/
def GeometricFiniteArtinSystemExistenceUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∃! a : FiniteArtinFamily F.Carrier,
      GeometricFiniteArtinSystemRelation F T a

end Langlands.LocalClassField
