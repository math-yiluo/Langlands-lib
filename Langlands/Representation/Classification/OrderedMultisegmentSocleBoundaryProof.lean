import Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryStatement
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! # Boundary lemmas for ordered segment-socle existence

Exact proof of the three elementary boundary assertions.
The endpoint clause retains integral-twist freeness as its explicit premise.
-/

noncomputable section

open Module

namespace Langlands.Classification

universe uG uF uV

private theorem irreducible_self_socle
    {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    IsIrreducibleSocle ρ ρ := by
  let := hρ
  refine ⟨hρ, Representation.IntertwiningMap.id ρ, Function.injective_id, ?_⟩
  intro W _ _ π hπ j hj
  let := hπ
  let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  have hj0 : j ≠ 0 := by
    intro hzero
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    apply hj
    rw [hzero]
    rfl
  have hsurj := (Representation.IsIrreducible.surjective_or_eq_zero j).resolve_right hj0
  exact (LinearMap.range_eq_top.mpr hsurj).trans
    (LinearMap.range_eq_top.mpr Function.surjective_id).symm

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual rank-zero product is its own strong socle for every supplied datum. -/
theorem orderedMultisegmentSocle_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0)
    (ho : d.IsPrecedenceOrdered) (hs : d.HasSegmentSocles) :
    d.IsZelevinskySocle d.induced := by
  let := T.topology
  exact ⟨ho, hs, irreducible_self_socle _
    (rankZeroNormalizedProduct_isIrreducible F T d.shape
      (fun i => (d.blocks i).representation))⟩

/-- Every actual product of the supplied segment-socle blocks is nonzero. -/
theorem segmentSocleProduct_nontrivial
    {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hs : d.HasSegmentSocles) :
    letI := T.topology
    Nontrivial d.induced := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let ρ := fun i => (d.blocks i).representation
  let b := fun i => Basis.ofVectorSpace ℂ (d.blocks i)
  let Bt := Basis.piTensorProduct b
  have hp : ∀ i, Nonempty (Basis.ofVectorSpaceIndex ℂ (d.blocks i)) := by
    intro i
    obtain ⟨_, _, hρ, _, _, _⟩ := hs i
    let : Representation.IsIrreducible (ρ i) := hρ
    let : Nontrivial (d.blocks i) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ
        (GeneralLinear (d.segments i).degree F.Carrier)) (ρ i).asModule
    exact (b i).index_nonempty
  let v := Bt (fun i => Classical.choice (hp i))
  have hv : v ≠ 0 := Bt.ne_zero _
  let σP := twist (T.parabolicHalfModulus d.shape)
    ((d.shape.blockTensor ρ).comp (d.shape.leviProjection F.Carrier))
  have hσ : IsSmooth (d.shape.blockTensor ρ) :=
    FiniteTensor.isSmooth_external ρ (fun i => (d.blocks i).isSmooth)
  have hσP : IsSmooth σP :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus d.shape)).mpr
      (isSmooth_comp _ (d.shape.leviProjectionContinuous F.Carrier).continuous hσ)
  have hsurj : Function.Surjective
      (fun f : d.induced => Induction.eval _ σP f 1) := by
    intro w
    refine ⟨(Induction.compactLocalSection _ σP hσP 1 w Set.univ
      isOpen_univ (Set.mem_univ _)).val, ?_⟩
    exact Induction.compactLocalSection_apply _ σP hσP 1 w Set.univ
      isOpen_univ (Set.mem_univ _)
  obtain ⟨f, hf⟩ := hsurj v
  refine ⟨⟨f, 0, ?_⟩⟩
  intro hf0
  apply hv
  rw [← hf, hf0]
  rfl

/-- Forward juxtaposition is an instance of the actual precedence relation. -/
private theorem segmentPrecedes_of_endpoint_eq
    (hfree : CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : PadicField.TopologicalData.Segment.{uV, uF} T}
    (hend : Γ.base = Δ.last.twist 1) : Δ.Precedes Γ := by
  have hcoordΔ := Δ.hasIntegralCoordinates_self
  have hcoordΓ : Γ.HasIntegralCoordinates Δ.base (Δ.length : ℤ)
      ((Δ.length : ℤ) + Γ.length - 1) := by
    refine ⟨?_, rfl⟩
    rw [hend, PadicField.TopologicalData.Segment.last,
      PadicField.TopologicalData.Segment.member,
      PadicField.TopologicalData.CuspidalDatum.twist_twist]
    congr 1
    have hlen := Δ.length_pos
    rw [Nat.cast_sub (by omega : 1 ≤ Δ.length)]
    push_cast
    ring
  apply hcoordΔ.precedes_of_intervalPrecedes hfree hcoordΓ
  have hΔ := Δ.length_pos
  have hΓ := Γ.length_pos
  exact ⟨by omega, by omega, by omega⟩

/-- Every supplied nonprecedence order satisfies the endpoint condition of
Zelevinsky 6.2, using only the explicit integral-twist-freeness input. -/
theorem precedenceOrdered_endpointSeparated
    (hfree : CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {r : ℕ} (segments : Fin r → PadicField.TopologicalData.Segment.{uV, uF} T)
    (ho : T.IsPrecedenceOrdered segments) :
    ∀ i j : Fin r, i < j → (segments j).base ≠ (segments i).last.twist 1 := by
  intro i j hij heq
  exact ho i j hij (segmentPrecedes_of_endpoint_eq F T hfree heq)

/-- Exact elementary boundary theorem for actual segment-socle products. -/
theorem orderedMultisegmentSocleBoundary :
    OrderedMultisegmentSocleBoundary.{uF, uV} F T := by
  let := T.topology
  refine ⟨?_, ?_, ?_⟩
  · intro d ho hs
    exact orderedMultisegmentSocle_rankZero.{uF, uV} F T d ho hs
  · intro n d hs
    exact segmentSocleProduct_nontrivial.{uF, uV} F T d hs
  · intro hfree r segments ho
    exact precedenceOrdered_endpointSeparated.{uF, uV} F T hfree segments ho

end Langlands.Classification
