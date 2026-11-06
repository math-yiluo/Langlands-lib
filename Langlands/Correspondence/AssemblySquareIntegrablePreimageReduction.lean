import Langlands.Correspondence.AssemblySquareIntegrableStatement
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Weil.Representation.IsomorphismInvarianceProof
import Langlands.WeilDeligne.IrreducibleBlockIndecomposable

/-!
# Essentially square-integrable assembly images, assuming head classification

A segment head is the Langlands head of the one-segment multisegment. Bernstein's
classification (proved) makes an essentially square-integrable head a segment head,
so head classification forces the assembled multisegment to have one segment. The
parameter is then one block with irreducible Weil factor, hence indecomposable.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands

namespace PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

/-- The one-segment product datum with segment `Δ` and block `π`. -/
def singleton (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :
    SegmentProductDatum.{uV, uF} T Δ.degree :=
  ⟨1, fun _ => Δ, by simp, fun _ => π⟩

@[simp]
theorem singleton_multisegment (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :
    (singleton Δ π).multisegment = {Δ} := by
  simp [singleton, multisegment]

end SegmentProductDatum

namespace Multisegment

/-- A segment head is a Langlands head of the one-segment multisegment. -/
theorem isLanglandsHead_singleton (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) :
    ({Δ} : Multisegment.{uV, uF} T).IsLanglandsHead π := by
  let := T.topology
  let d := SegmentProductDatum.singleton Δ π
  refine ⟨d, SegmentProductDatum.singleton_multisegment Δ π, ?_, fun _ => hπ, ?_⟩
  · intro i j hij
    have hi : (i : ℕ) < 1 := i.isLt
    have hj : (j : ℕ) < 1 := j.isLt
    have hlt : (i : ℕ) < j := hij
    omega
  · obtain ⟨A, hA, hhead⟩ := hπ
    have hirr : Representation.IsIrreducible π.representation := hhead.1
    have e : d.induced ≅ π :=
      Classification.SegmentProductOrderedAssembly.singletonIso d rfl (0 : Fin 1)
    exact Classification.IsIrreducibleHead.of_equiv (SmoothRep.equivOfIso e).symm
      (Classification.isIrreducibleHead_self π.representation hirr)

/-- The same along an equality of the segment degree with the rank. -/
theorem isLanglandsHead_singleton_of_degree_eq (Δ : Segment.{uV, uF} T) {k : ℕ}
    (h : Δ.degree = k)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (hπ : T.IsSegmentHead Δ (h.symm ▸ π)) :
    ({Δ} : Multisegment.{uV, uF} T).IsLanglandsHead π := by
  subst h
  exact isLanglandsHead_singleton Δ π hπ

end Multisegment

end PadicField.TopologicalData

namespace Correspondence

universe uF uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyPreimageFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyPreimageGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A representation in an irreducible Weil class is irreducible. -/
theorem isIrreducible_of_classOf_eq {d : ℕ}
    (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
    (h : FiniteRepresentation.classOf B = weilClassForget F σ) :
    Representation.IsIrreducible B.representation := by
  obtain ⟨⟨C, hC⟩, hCσ⟩ := Quotient.exists_rep σ.val
  have h1 : FiniteRepresentation.classOf B = FiniteRepresentation.classOf C := by
    rw [h]
    change FiniteRepresentation.forgetPropertyClass _ σ.val = _
    rw [← hCσ]
    rfl
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff B C).mp h1
  exact (Weil.IsomorphismInvariance.irreducible_iff e).mpr hC.2

/-- Henniart 2002 §§2.6-2.9, assuming the multisegment head classification: an
essentially square-integrable assembly image comes from an indecomposable
parameter. -/
theorem assemblySquareIntegrablePreimage_of_headClassification
    (hclass : Classification.MultisegmentHeadClassification.{uF, uA} F
      F.canonicalTopologicalData) :
    AssemblySquareIntegrablePreimageStatement.{uF, uP, uA} F := by
  intro c0 n D A hD hA
  obtain ⟨r, d, m, σ, ⟨B, W, hB, hW, ⟨e⟩⟩, A', J, hA'A, hJ, ⟨eJ⟩⟩ := hD
  obtain ⟨eA⟩ := (automorphicClassOf_eq_iff F A' A).mp hA'A
  have hJirr : Representation.IsIrreducible J.representation := by
    obtain ⟨_, -, -, -, h⟩ := hJ
    exact h.1
  have hJesi : F.canonicalTopologicalData.IsEssentiallySquareIntegrable J.representation :=
    (isEssentiallySquareIntegrable_iff_of_equiv (T := F.canonicalTopologicalData)
      (eJ.trans eA)).mpr hA
  obtain ⟨Δ, hΔn, hΔ⟩ :=
    (Classification.segmentEssentialSquareIntegrableClassification.{uF, uA} F
      F.canonicalTopologicalData (n : ℕ) n.pos J hJirr).mp hJesi
  have hsingle : ({Δ} : F.canonicalTopologicalData.Multisegment).IsLanglandsHead J :=
    Multisegment.isLanglandsHead_singleton_of_degree_eq Δ hΔn J hΔ
  have hlift : (multisegmentOf F c0 σ m).universeLift.IsLanglandsHead J :=
    (Multisegment.isLanglandsHead_universeLift_iff _ J).mpr hJ
  have heq : (multisegmentOf F c0 σ m).universeLift = {Δ} :=
    (hclass (n : ℕ) _ _ J J hlift hsingle).mpr ⟨Iso.refl J⟩
  have hr : r = 1 := by
    have h := congrArg Multiset.card heq
    simpa [Multisegment.universeLift, multisegmentOf] using h
  subst hr
  have hB0 : Representation.IsIrreducible (B 0).representation :=
    isIrreducible_of_classOf_eq F (B 0) (σ 0) (hB 0)
  refine ⟨W, hW, ?_⟩
  exact WeilDeligneRepresentation.Blocks.IsIndecomposable.of_equiv e
    (WeilDeligneRepresentation.Blocks.IsIndecomposable.of_equiv
      (WeilDeligneRepresentation.directSumFinOneEquiv _).symm
      (WeilDeligneRepresentation.Blocks.isIndecomposable_block hB0 (m 0)))

end Correspondence

end Langlands
