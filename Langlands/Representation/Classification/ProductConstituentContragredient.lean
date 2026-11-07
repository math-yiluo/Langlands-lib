import Langlands.Representation.Classification.ConstituentAutomorphismTransport
import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.Representation.Parabolic.ContragredientReversal
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof

/-! Strong constituent duality for reversed normalized products. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

set_option maxHeartbeats 800000 in
/-- Inverse transpose of a product of irreducible smooth blocks is the
reversed product of their actual smooth duals. -/
theorem nonempty_inverseTranspose_dualProductEquiv {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hirr : letI := T.topology
      ∀ i, Representation.IsIrreducible (σ i).representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
      fun k => T.generalLinearTopologicalGroup k
    Nonempty (Representation.Equiv
      ((T.normalizedProductInduced B (fun i => (σ i).representation)).comp
        (inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced B.reverse
        (fun i => smoothContragredient (σ i.rev).representation))) := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨A⟩ := Parabolic.normalizedProductInverseTranspose T n hn B
    (fun i => σ i) (fun i => (σ i).representation) (fun i => (σ i).isSmooth)
  have hblock (i : Fin B.length) : Nonempty (Representation.Equiv
      ((σ i).representation.comp (inverseTranspose (B.size i) F.Carrier).toMonoidHom)
      (smoothContragredient (σ i).representation)) :=
    Parabolic.gelfandKazhdan_of_topologicalData gelfandKazhdanContragredient.{uF, uV} T
      (B.size i) (B.positive i) (σ i).representation
      (CuspidalSupport.cuspidalEmbedding F T (B.size i) (σ i) (hirr i)).1 (hirr i)
  let C := T.normalizedProductInducedEquiv B.reverse
    (V := fun i => σ i.rev) (W := fun i => SmoothDual (σ i.rev).representation)
    (fun i => (hblock i.rev).some)
  exact ⟨A.trans C⟩

/-- Strong socles dualize to strong socles in the reversed dual product. -/
theorem IsIrreducibleSocle.contragredient_product {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hirr : letI := T.topology
      ∀ i, Representation.IsIrreducible (σ i).representation)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : letI := T.topology; IsIrreducibleSocle
      (T.normalizedProductInduced B (fun i => (σ i).representation)) π.representation) :
    letI := T.topology
    letI : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
      fun k => T.generalLinearTopologicalGroup k
    IsIrreducibleSocle (T.normalizedProductInduced B.reverse
      (fun i => smoothContragredient (σ i.rev).representation))
      (smoothContragredient π.representation) := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨A⟩ := nonempty_inverseTranspose_dualProductEquiv T hn B σ hirr
  obtain ⟨E⟩ := Parabolic.gelfandKazhdan_of_topologicalData
    gelfandKazhdanContragredient T n hn π.representation
    (CuspidalSupport.cuspidalEmbedding F T n π h.1).1 h.1
  exact ((h.comp_mulEquiv (inverseTranspose n F.Carrier)).of_equiv A).of_targetEquiv E

/-- Strong heads dualize to strong heads in the reversed dual product. -/
theorem IsIrreducibleHead.contragredient_product {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hirr : letI := T.topology
      ∀ i, Representation.IsIrreducible (σ i).representation)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : letI := T.topology; IsIrreducibleHead
      (T.normalizedProductInduced B (fun i => (σ i).representation)) π.representation) :
    letI := T.topology
    letI : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
      fun k => T.generalLinearTopologicalGroup k
    IsIrreducibleHead (T.normalizedProductInduced B.reverse
      (fun i => smoothContragredient (σ i.rev).representation))
      (smoothContragredient π.representation) := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨A⟩ := nonempty_inverseTranspose_dualProductEquiv T hn B σ hirr
  obtain ⟨E⟩ := Parabolic.gelfandKazhdan_of_topologicalData
    gelfandKazhdanContragredient T n hn π.representation
    (CuspidalSupport.cuspidalEmbedding F T n π h.1).1 h.1
  exact ((h.comp_mulEquiv (inverseTranspose n F.Carrier)).of_equiv A).of_targetEquiv E

end Langlands.Classification
