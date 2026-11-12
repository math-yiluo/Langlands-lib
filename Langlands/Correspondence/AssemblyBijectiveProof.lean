import Langlands.Correspondence.AssemblyBijectiveReduction
import Langlands.Correspondence.AssemblyUniqueness
import Langlands.Representation.Classification.MultisegmentHeadExhaustionProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationReduction
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof
import Langlands.Representation.Classification.SegmentSpecialParameterUniquenessProof

/-!
# Bijectivity of the assembly

The assembly of a rankwise bijective supercuspidal map is rankwise bijective.
Injectivity is the published reduction `assembly_injective`, fed with the
multiset head classification, which follows from the published ordered head
classification. Surjectivity uses the published head exhaustion and the
unconditional uniqueness `isAssembledFrom_unique` of the assembled class.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyBijectiveFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyBijectiveGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The multiset form of the head classification for the canonical topology:
heads of two multisegments are isomorphic exactly when the multisegments agree.
Each head is a quotient of an ordered datum with that multisegment, so this is
the ordered classification, proved from the square-integrable classification
and the uniqueness of segment parameters. -/
theorem multisegmentHeadClassification_canonical :
    Classification.MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData := by
  intro n a b π π' ⟨d, hd, hπ⟩ ⟨d', hd', hπ'⟩
  subst hd hd'
  exact Classification.orderedMultisegmentHeadClassification_of_squareIntegrable.{uF, uA}
    F F.canonicalTopologicalData
    (Classification.squareIntegrableLanglandsClassification.{uF, uA} F _)
    (Classification.segmentSpecialParameterUniqueness.{uF, uA} F _)
    n d d' π π' hπ.isLanglandsQuotient hπ'.isLanglandsQuotient

/-- Surjectivity: with `c0` surjective in every rank, the assembly `c` of `c0` is
surjective in every rank. Every class is the head of a multisegment, whose
segment bases come from `c0`; the resulting block sum `D` has the given class as
an assembled class, which is therefore `c n D`. -/
theorem assembly_surjective_of_surjective
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc0 : ∀ k, Function.Surjective (c0 k)) (hc : IsAssemblyOf F c0 c) (n : ℕ+) :
    Function.Surjective (c n) := by
  intro π
  obtain ⟨A, rfl⟩ := automorphicClass_has_representative F π
  let J := SmoothRep.universeLift.{uF} A.obj
  have hJ : Representation.IsIrreducible J.representation :=
    (SmoothRep.isIrreducible_universeLift_iff A.obj).mpr A.property.1
  obtain ⟨b, hb, hbJ⟩ :=
    Classification.multisegmentHeadExhaustion.{uF, uA} F F.canonicalTopologicalData n J hJ
  obtain ⟨a, rfl⟩ := Multisegment.universeLift_surjective b
  rw [Multisegment.isLanglandsHead_universeLift_iff] at hbJ
  rw [Multisegment.universeLift_degree] at hb
  obtain ⟨r, d, m, σ, rfl⟩ := exists_multisegmentOf_eq F hc0 a
  rw [degree_multisegmentOf] at hb
  let D := blockSumClass F σ m n hb.symm
  have h2 : IsAssembledFrom F c0 D (automorphicClassOf F A) :=
    ⟨r, d, m, σ, isBlockSum_blockSumClass F σ m n hb.symm, A, J, rfl, hbJ,
      ⟨(SmoothRep.universeLiftEquiv A.obj).symm⟩⟩
  exact ⟨D, isAssembledFrom_unique F c0 (hc n D) h2⟩

/-- The assembly of a rankwise bijective supercuspidal map is rankwise bijective. -/
theorem assemblyBijective : AssemblyBijectiveStatement.{uF, uP, uA} F :=
  fun _ _ hc0 hc n =>
    ⟨assembly_injective F (multisegmentHeadClassification_canonical.{uF, uA} F)
        (fun k => (hc0 k).1) hc n,
      assembly_surjective_of_surjective F (fun k => (hc0 k).2) hc n⟩

end Langlands.Correspondence
