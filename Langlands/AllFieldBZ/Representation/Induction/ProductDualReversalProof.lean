import Langlands.AllFieldBZ.Representation.Induction.ProductDualReversalStatement
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeProductAnalytics
import Langlands.AllFieldBZ.Representation.Classification.CuspidalProductContragredient
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Contragredient.LocalFieldGelfandKazhdan
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly

/-! Actual normalized induction duality with reversal through inverse transpose. -/

noncomputable section

namespace Langlands.AllFieldBZ.Parabolic

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData
open Langlands.AllFieldBZ.Classification.CuspidalProductContragredient
  (nonempty_contragredient_productEquiv)

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Gelfand–Kazhdan as a representation equivalence in any positive rank. -/
theorem nonempty_inverseTranspose_contragredient {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsAdmissible ρ → Representation.IsIrreducible ρ →
      Nonempty (Representation.Equiv
        (ρ.comp (inverseTranspose n F.Carrier).toMonoidHom) (smoothContragredient ρ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m + 1)
  intro hadm hirr
  obtain ⟨e, he⟩ := LocalField.gelfandKazhdanContragredient F.Carrier m V ρ hadm hirr
  exact ⟨Representation.Equiv.mk e (fun g => LinearMap.ext (he g))⟩

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual inverse-transpose pullback and reversed smooth dual agree. -/
theorem productDualReversal : ProductDualReversalStatement.{uF, uV} F T := by
  let := T.topology
  intro n B A hA
  let := T.generalLinearTopologicalGroup n
  let σ := fun i => (A i).representation
  let τ := fun i : Fin B.reverse.length => (A i.rev).representation
  have hadm (i : Fin B.length) : IsAdmissible (σ i) :=
    (CuspidalSupport.cuspidalEmbedding F T (B.size i) (A i) (hA i)).1
  have hgk (i : Fin B.reverse.length) := nonempty_inverseTranspose_contragredient T
    (B.positive i.rev) (τ i) (hadm i.rev) (hA i.rev)
  let reversePullback := AllField.GodementJacquet.inverseTransposeProductReversalEquiv T B σ
    (fun i => (A i).isSmooth)
  let induceBlockDuals := T.normalizedProductInducedEquiv B.reverse
    (fun i => Classical.choice (hgk i))
  obtain ⟨dualProduct⟩ := nonempty_contragredient_productEquiv T B.reverse τ (fun i => hadm i.rev)
  exact ⟨Langlands.Parabolic.equivTrans reversePullback
    (Langlands.Parabolic.equivTrans induceBlockDuals
      (Langlands.Parabolic.equivSymm dualProduct))⟩

end Langlands.AllFieldBZ.Parabolic
