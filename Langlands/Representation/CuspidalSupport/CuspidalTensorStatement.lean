import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Tensor-factor interfaces for the multiset form of cuspidal support. -/

namespace Langlands.CuspidalSupport

open GeneralLinear PadicField.TopologicalData

universe uV uF

/-- The external tensor product of irreducible supercuspidal block factors
is irreducible and cuspidal on the actual product Levi. -/
def GLCuspidalTensorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    letI := T.topology
    ∀ (B : BlockShape n)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
      let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation

/-- Association of two external tensor products of supercuspidal factors
forces equality of their multisets of cuspidal data, including multiplicity. -/
def GLCuspidalTensorAssociationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    letI := T.topology
    ∀ (k l : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T)
      (ρ' : Fin l → CuspidalDatum.{uV, uF} T)
      (h : ∑ i, (ρ i).rank = n) (h' : ∑ i, (ρ' i).rank = n)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
      (A' : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ' i).rank)),
      (∀ i, (ρ i).IsRepresentedBy (A i)) →
      (∀ i, (ρ' i).IsRepresentedBy (A' i)) →
      RepresentationsAssociated (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h')
        (FiniteTensor.external (fun i => (A i).obj.representation))
        (FiniteTensor.external (fun i => (A' i).obj.representation)) →
      (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) =
        (List.ofFn ρ' : Multiset (CuspidalDatum.{uV, uF} T))

/-- The two tensor-factor interfaces needed to pass from Levi association
to uniqueness of the multiset of supercuspidal factors. -/
def GLCuspidalTensorInterfacesStatement : Prop :=
  GLCuspidalTensorStatement.{uV, uF} ∧
    GLCuspidalTensorAssociationStatement.{uV, uF}

end Langlands.CuspidalSupport
