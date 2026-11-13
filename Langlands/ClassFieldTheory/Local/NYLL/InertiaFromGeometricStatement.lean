import Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement

/-! # The inertia clause from the geometric residue clause -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- For a finite extension of p-adic fields with arbitrary supplied realizations,
every isomorphism from the actual norm quotient to the actual Galois group that
satisfies the geometric residue clause of
`Langlands.LocalClassField.FiniteAbelianReciprocity` also satisfies its inertia
clause: the images of the classes of order-zero units are exactly the
automorphisms fixing every integral residue class. -/
def InertiaFromGeometricStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData)
    (r : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range) ≃*
      Gal(E.Carrier/F.Carrier)),
    (∀ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 1 →
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation
          ((r (QuotientGroup.mk a)).symm x - x ^ TF.residueCardinality) < 1) →
    ∀ σ : Gal(E.Carrier/F.Carrier),
      (∃ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 0 ∧ r (QuotientGroup.mk a) = σ) ↔
        ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
          TE.discreteValuation (σ x - x) < 1

end Langlands.LocalClassField.NYLL
