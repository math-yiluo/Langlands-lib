import Langlands.Correspondence.AssemblyMultisegments
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Weil.Local.BlockSumParameter

/-!
# Bijectivity of the assembly, reduced to the multisegment classification

The assembly of a rankwise bijective supercuspidal map is rankwise bijective,
assuming three published propositions that are not proved here: the head
classification and head exhaustion for multisegments (at carrier universe
`max uF uA`), and the well-definedness of the assembly.

The classification propositions quantify over multisegments in the larger
universe; the lift of multisegments from `uA` is surjective by the small-model
realization of irreducible smooth representations.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Every supercuspidal class with carriers in `Type (max uF uV)` is a lift: its
representative has an equivalent irreducible realization in `Type uV`. -/
theorem supercuspidalClass_universeLift_surjective (n : ℕ) :
    letI := T.topology
    Function.Surjective
      (GeneralLinear.SupercuspidalClass.universeLift.{uF, uV} (F := F.Carrier) (n := n)) := by
  let := T.topology
  intro b
  induction b using Quotient.inductionOn with
  | h B =>
    obtain ⟨σ, hσ, ⟨e⟩⟩ :=
      padicIrreducibleSmoothSmallRealization.{uF, max uF uV, uV} p F T n B.obj B.property.1
    let A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n) :=
      ⟨σ, hσ, GeneralLinear.isSupercuspidal_of_equiv e B.property.2⟩
    refine ⟨A.isoClass, Quotient.sound ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (SmoothRep.mkIso
      ((GeneralLinear.SupercuspidalRep.universeLiftEquiv A).symm.trans e.symm))

variable {T}

/-- Every cuspidal datum with carriers in `Type (max uF uV)` is a lift. -/
theorem CuspidalDatum.universeLift_surjective :
    Function.Surjective
      (CuspidalDatum.universeLift : CuspidalDatum.{uV, uF} T → CuspidalDatum.{max uF uV, uF} T) := by
  rintro ⟨r, hr, b⟩
  obtain ⟨a, rfl⟩ := supercuspidalClass_universeLift_surjective.{uF, uV} T r b
  exact ⟨⟨r, hr, a⟩, rfl⟩

/-- Every segment with carriers in `Type (max uF uV)` is a lift. -/
theorem Segment.universeLift_surjective :
    Function.Surjective
      (Segment.universeLift : Segment.{uV, uF} T → Segment.{max uF uV, uF} T) := by
  intro Δ'
  obtain ⟨ρ, hρ⟩ := CuspidalDatum.universeLift_surjective Δ'.base
  exact Segment.exists_universeLift_eq Δ' ρ hρ.symm

/-- Every multisegment with carriers in `Type (max uF uV)` is a lift. -/
theorem Multisegment.universeLift_surjective :
    Function.Surjective
      (Multisegment.universeLift : Multisegment.{uV, uF} T → Multisegment.{max uF uV, uF} T) :=
  Multiset.map_surjective_of_surjective Segment.universeLift_surjective

end PadicField.TopologicalData

namespace Correspondence

universe uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyReductionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyReductionGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A representative of an irreducible Weil class of rank `d + 1` has rank `d + 1`. -/
theorem rank_eq_of_classOf_eq {k : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F k)
    {B : Weil.Local.LocalWeilRepresentation.{uF, uP} F}
    (hB : FiniteRepresentation.classOf B = weilClassForget F σ) : B.rank = k := by
  rw [← FiniteRepresentation.classRank_classOf, hB]
  exact σ.property

/-- Every irreducible Weil class has a continuous irreducible representative. -/
theorem exists_representative {k : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F k) :
    ∃ B : Weil.Local.LocalWeilRepresentation.{uF, uP} F,
      (B.IsContinuous ∧ B.IsIrreducible) ∧
        FiniteRepresentation.classOf B = weilClassForget F σ := by
  obtain ⟨⟨B, hB⟩, h⟩ := Quotient.exists_rep σ.val
  refine ⟨B, hB, ?_⟩
  change FiniteRepresentation.classOf B =
    FiniteRepresentation.forgetPropertyClass _ σ.val
  rw [← h]
  rfl

/-- The parameter class `⊕_i σ_i ⊗ Sp(m_i + 1)` of rank `n = ∑ (d_i + 1)(m_i + 1)`:
the block-sum parameter class on chosen continuous irreducible representatives of
the irreducible Weil classes `σ_i`. -/
def blockSumClass {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ) (n : ℕ+)
    (hn : (n : ℕ) = ∑ i, (d i + 1) * (m i + 1)) : WeilDeligneClass.{uF, uP} F n :=
  let D0 := Weil.Local.blockSumParameterClass F (fun i => (exists_representative F (σ i)).choose)
    (fun i => (exists_representative F (σ i)).choose_spec.1) fun i => m i + 1
  ⟨D0.val, D0.property.trans <| by
    rw [hn]
    exact Finset.sum_congr rfl fun i _ => by
      rw [rank_eq_of_classOf_eq F (σ i) (exists_representative F (σ i)).choose_spec.2]
      rfl⟩

/-- `blockSumClass F σ m n hn` is the block sum `⊕_i σ_i ⊗ Sp(m_i + 1)`. -/
theorem isBlockSum_blockSumClass {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ) (n : ℕ+)
    (hn : (n : ℕ) = ∑ i, (d i + 1) * (m i + 1)) :
    IsBlockSum F σ m (blockSumClass F σ m n hn) :=
  ⟨fun i => (exists_representative F (σ i)).choose, _,
    fun i => (exists_representative F (σ i)).choose_spec.2,
    Weil.Local.forget_blockSumParameterClass F _
      (fun i => (exists_representative F (σ i)).choose_spec.1) _ |>.symm,
    ⟨WeilDeligneRepresentation.Equiv.refl _⟩⟩

/-- Injectivity: with `c0` injective in every rank, the assembly `c` of `c0` is
injective in every rank, assuming the head classification. -/
theorem assembly_injective
    (hHC : Classification.MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc0 : ∀ k, Function.Injective (c0 k)) (hc : IsAssemblyOf F c0 c) (n : ℕ+) :
    Function.Injective (c n) := by
  intro D D' h
  obtain ⟨r, d, m, σ, hB, A, J, hA, hJ, ⟨eJ⟩⟩ := hc n D
  obtain ⟨r', d', m', σ', hB', A', J', hA', hJ', ⟨eJ'⟩⟩ := hc n D'
  rw [h, ← hA'] at hA
  obtain ⟨eA⟩ := (automorphicClassOf_eq_iff F A A').mp hA
  rw [← Multisegment.isLanglandsHead_universeLift_iff] at hJ hJ'
  have hms := Multisegment.universeLift_injective
    ((hHC _ _ _ J J' hJ hJ').mpr ⟨SmoothRep.mkIso ((eJ.trans eA).trans eJ'.symm)⟩)
  obtain ⟨e, he⟩ := multisegmentOf_matching F hc0 hms
  exact IsBlockSum.eq_of_matching F hB hB' e he

/-- Surjectivity: with `c0` surjective in every rank, the assembly `c` of `c0` is
surjective in every rank, assuming head exhaustion and well-definedness. -/
theorem assembly_surjective
    (hHE : Classification.MultisegmentHeadExhaustion.{uF, uA} F F.canonicalTopologicalData)
    (hWD : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc0 : ∀ k, Function.Surjective (c0 k)) (hc : IsAssemblyOf F c0 c) (n : ℕ+) :
    Function.Surjective (c n) := by
  intro π
  obtain ⟨A, rfl⟩ := automorphicClass_has_representative F π
  let J := SmoothRep.universeLift.{uF} A.obj
  have hJ : Representation.IsIrreducible J.representation :=
    (SmoothRep.isIrreducible_universeLift_iff A.obj).mpr A.property.1
  obtain ⟨b, hb, hbJ⟩ := hHE n J hJ
  obtain ⟨a, rfl⟩ := Multisegment.universeLift_surjective b
  rw [Multisegment.isLanglandsHead_universeLift_iff] at hbJ
  rw [Multisegment.universeLift_degree] at hb
  obtain ⟨r, d, m, σ, rfl⟩ := exists_multisegmentOf_eq F hc0 a
  rw [degree_multisegmentOf] at hb
  let D := blockSumClass F σ m n hb.symm
  have h2 : IsAssembledFrom F c0 D (automorphicClassOf F A) :=
    ⟨r, d, m, σ, isBlockSum_blockSumClass F σ m n hb.symm, A, J, rfl, hbJ,
      ⟨(SmoothRep.universeLiftEquiv A.obj).symm⟩⟩
  exact ⟨D, (hWD c0 n D).unique (hc n D) h2⟩

/-- The assembly of a rankwise bijective supercuspidal map is rankwise bijective,
assuming the head classification, head exhaustion and well-definedness. -/
theorem assemblyBijective_of_classification
    (hHC : Classification.MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData)
    (hHE : Classification.MultisegmentHeadExhaustion.{uF, uA} F F.canonicalTopologicalData)
    (hWD : AssemblyWellDefinedStatement.{uF, uP, uA} F) :
    AssemblyBijectiveStatement.{uF, uP, uA} F := fun _ _ hc0 hc n =>
  ⟨assembly_injective F hHC (fun k => (hc0 k).1) hc n,
    assembly_surjective F hHE hWD (fun k => (hc0 k).2) hc n⟩

end Correspondence

end Langlands
