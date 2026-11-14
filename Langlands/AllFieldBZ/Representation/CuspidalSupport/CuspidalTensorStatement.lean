import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.CuspidalSupport.CuspidalTensorStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalTensorStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CuspidalTensorStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uV uF

/-- The external tensor product of irreducible supercuspidal block factors
is irreducible and cuspidal on the actual product Levi. -/
def GLCuspidalTensorStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    letI := T.topology
    ∀ (B : BlockShape n)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
      let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation

/-- Association of two external tensor products of supercuspidal factors
forces equality of their multisets of cuspidal data, including multiplicity. -/
def GLCuspidalTensorAssociationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    letI := T.topology
    ∀ (k l : ℕ) (ρ : Fin k → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)
      (ρ' : Fin l → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)
      (h : ∑ i, (ρ i).rank = n) (h' : ∑ i, (ρ' i).rank = n)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
      (A' : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ' i).rank)),
      (∀ i, (ρ i).IsRepresentedBy (A i)) →
      (∀ i, (ρ' i).IsRepresentedBy (A' i)) →
      RepresentationsAssociated (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h')
        (FiniteTensor.external (fun i => (A i).obj.representation))
        (FiniteTensor.external (fun i => (A' i).obj.representation)) →
      (List.ofFn ρ : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)) =
        (List.ofFn ρ' : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T))

end Langlands.AllFieldBZ.CuspidalSupport
