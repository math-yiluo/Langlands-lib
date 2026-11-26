import Langlands.BaseChange.TwistedCharacter.Head
import Langlands.BaseChange.TwistedCharacter.StableLanglandsData
import Langlands.BaseChange.TwistedCharacter.LanglandsHeadOrder
import Langlands.Representation.Classification.MultisegmentHeadExhaustionProof

/-! # Spanning twisted irreducible traces by stable standard traces -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory Classification GeneralLinear HarmonicAnalysis MeasureTheory
open PadicField.TopologicalData

universe u v z

section Standard

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier) {n : ℕ}
  (t : T.TemperedLanglandsDatum.{z} n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual normalized induction of the twisting isomorphisms of the
tempered blocks, after their real determinant twists. -/
def temperedStandardSigmaIntertwiner
    (A : letI := T.topology
      ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation) :
    letI := T.topology
    SigmaIntertwiner σ n t.standardModule.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let S (i : Fin t.shape.length) := (T.twistedBlocks t.shape t.blocks t.exponent i).representation
  let B (i : Fin t.shape.length) : SigmaIntertwiner σ (t.shape.size i) (S i) :=
    twistTwistedIntertwiner (entrywiseAut σ (t.shape.size i))
      (T.determinantPowerCharacter (t.shape.size i) (t.exponent i))
      (determinantPowerCharacter_entrywiseAut T hModule σ _ _) (A i)
  rw [TemperedLanglandsDatum.standardModule_representation]
  exact inducedSigmaIntertwiner σ t.shape B

/-- The actual normalized standard module is admissible. -/
theorem temperedStandard_isAdmissible :
    letI := T.topology
    IsAdmissible t.standardModule.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [TemperedLanglandsDatum.standardModule_representation]
  exact isAdmissible_normalizedProductInduced t.shape _
    (fun i => (RegularHeadExistence.twistedBlock_admissible_finiteLength T t i).1)

end Standard

/-- Containing the actual twisted distributions of the σ-stable ordered
tempered standard data suffices for containing every σ-stable irreducible
twisted distribution of positive rank. -/
def StableLanglandsTraceSpanStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
    (E : PadicField.{v} p) [Algebra F E.Carrier] (T : E.TopologicalData),
    letI := T.topology
    ∀ (hModule : IsModuleTopology F E.Carrier) (σ : E.Carrier ≃ₐ[F] E.Carrier)
      (n : ℕ), 0 < n →
      letI := T.generalLinearTopologicalGroup n
      ∀ [T2Space (GeneralLinear n E.Carrier)]
        [LocallyCompactSpace (GeneralLinear n E.Carrier)]
        [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
        [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
        (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
        [μ.IsMulLeftInvariant] (L : Submodule ℂ (Distribution (GeneralLinear n E.Carrier))),
        (∀ (t : T.TemperedLanglandsDatum.{max v z} n)
          (A : ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation),
          twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
            (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap ∈ L) →
        ∀ (π : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier))
          (hπ : π.IsAdmissible), π.IsIrreducible →
          ∀ A : SigmaIntertwiner σ n π.representation,
            twistedDistribution μ π.representation hπ A.toLinearMap ∈ L

set_option maxHeartbeats 800000 in
/-- Induct on the head multisegment using strict descent and additivity along
the actual preserved head kernel. -/
theorem stableLanglandsTraceSpan : StableLanglandsTraceSpanStatement.{u,v,z} := by
  intro F _ _ p _ E _ T
  let := T.topology
  intro hModule σ n hn
  let := T.generalLinearTopologicalGroup n
  intro _ _ _ _ _ μ _ _ L hStandard
  have hAll (a : T.Multisegment.{max v z, v}) :
      ∀ (π : SmoothRep.{0,v,max v z} ℂ (GeneralLinear n E.Carrier))
        (hπ : π.IsAdmissible), a.IsLanglandsHead π →
        ∀ A : SigmaIntertwiner σ n π.representation,
          twistedDistribution μ π.representation hπ A.toLinearMap ∈ L := by
    induction a using (Multisegment.wellFounded_rankLT (T := T)).induction with
    | h a ih =>
      intro π hπ ha A
      have hπirr := Aubert.LanglandsHeadDuality.isIrreducible_of_isLanglandsHead E T ha
      obtain ⟨t, ht, hStable⟩ := exists_sigmaStable_temperedLanglandsHead.{u,v,z}
        F p E T hModule σ n hn π hπirr hπ ⟨A⟩
      obtain ⟨a', ha', hFin, hOrder⟩ := temperedLanglandsHeadOrder.{v,z} p E T n hn t π ht
      have haEq : a' = a :=
        (multisegmentHeadClassification E T n a' a π π ha' ha).mpr ⟨Iso.refl π⟩
      subst a'
      let B (i : Fin t.shape.length) := Classical.choice (hStable i)
      refine twistedDistribution_mem_of_irreducibleHead μ (entrywiseAut σ n) L
        t.standardModule (temperedStandard_isAdmissible T t) hFin
        (temperedStandardSigmaIntertwiner T hModule σ t B) (hStandard t B) π hπ ht A ?_
      intro D hD hDirr hSub AD
      obtain ⟨b, _, hb⟩ := multisegmentHeadExhaustion.{v,z} E T n D hDirr
      exact ih b (hOrder b D hb hSub) D hD hb AD
  intro π hπ hπirr A
  obtain ⟨a, _, ha⟩ := multisegmentHeadExhaustion.{v,z} E T n π hπirr
  exact hAll a π hπ ha A

end Langlands.BaseChange
