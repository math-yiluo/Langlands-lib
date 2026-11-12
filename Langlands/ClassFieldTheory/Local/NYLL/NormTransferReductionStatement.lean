import Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement

/-! # The transfer equation from norm compatibility

This proposition isolates the elementary step from the norm clause of
`Langlands.LocalClassField.FiniteAbelianNormTransfer` to its transfer clause.
It concerns arbitrary quotient equivalences; it provides no reciprocity map.
-/

namespace Langlands.LocalClassField.NYLL

universe u v w

/-- In a finite abelian tower `F ⊆ E ⊆ L`, every pair of quotient equivalences
for `L/F` and `L/E` that turns the norm `Eˣ → Fˣ` into the inclusion
`Gal(L/E) → Gal(L/F)` also turns scalar inclusion `Fˣ → Eˣ`, followed by that
Galois inclusion, into the `[E:F]`-th power map. -/
def NormCompatibleTransferStatement : Prop :=
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
    ∀ (rF : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := L.Carrier))).range)
        ≃ₜ* Gal(L.Carrier/F.Carrier))
      (rE : (E.Carrierˣ ⧸ (Units.map (Algebra.norm E.Carrier (S := L.Carrier))).range)
        ≃ₜ* Gal(L.Carrier/E.Carrier)),
      (∀ a : E.Carrierˣ,
        rF (QuotientGroup.mk (Units.map (Algebra.norm F.Carrier (S := E.Carrier)) a)) =
          (rE (QuotientGroup.mk a)).restrictScalars F.Carrier) →
      ∀ a : F.Carrierˣ,
        (rE (QuotientGroup.mk
          (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a))).restrictScalars
            F.Carrier =
          rF (QuotientGroup.mk a) ^ Module.finrank F.Carrier E.Carrier

end Langlands.LocalClassField.NYLL
