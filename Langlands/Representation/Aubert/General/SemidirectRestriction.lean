import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Aubert.General.SemidirectHaarModulus
import Langlands.Representation.Aubert.General.Conjugation

/-! # Restricting a semidirect decomposition to an intermediate subgroup -/

noncomputable section

universe u

open Topology MeasureTheory

namespace Langlands.Aubert.General.IsSemidirectDecomposition

variable {G : Type u} [Group G] {P M U Q : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hQP : Q ≤ P) (hUQ : U ≤ Q)

include h hQP hUQ

/-- A subgroup between the radical and parabolic inherits their decomposition. -/
theorem restrict : IsSemidirectDecomposition Q (M ⊓ Q) U := by
  refine ⟨inf_le_right, hUQ, hQP.trans h.le_normalizer, ?_⟩
  apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
  intro q
  let p : P := ⟨q, hQP q.property⟩
  let m : (M ⊓ Q).subgroupOf Q :=
    ⟨⟨h.projection p, h.projection_mem_of_radical_le hQP hUQ q⟩,
      (h.projection p).property, h.projection_mem_of_radical_le hQP hUQ q⟩
  refine ⟨m, h.projection_inv_mul_mem p, ?_⟩
  intro n hn
  apply Subtype.ext
  apply Subtype.ext
  exact (congrArg Subtype.val
    ((h.projection_eq_iff p ⟨((n : Q) : G), n.property.1⟩).mpr hn)).symm

/-- The intermediate projection is the restriction of the original one. -/
theorem restrict_projection (q : Q) :
    ((h.restrict hQP hUQ).projection q : G) =
      (h.projection ⟨q, hQP q.property⟩ : G) := by
  symm
  have he := (h.projection_eq_iff ⟨q, hQP q.property⟩
    ⟨((h.restrict hQP hUQ).projection q : G),
      ((h.restrict hQP hUQ).projection q).property.1⟩).mpr
      ((h.restrict hQP hUQ).projection_inv_mul_mem q)
  exact congrArg (fun m : M => (m : G)) he

variable [TopologicalSpace G]

/-- Continuity of the projection survives the intermediate restriction. -/
theorem continuous_restrict_projection (hp : Continuous h.projection) :
    Continuous (h.restrict hQP hUQ).projection := by
  have hc : Continuous (fun q : Q => h.projection ⟨q, hQP q.property⟩) :=
    hp.comp (continuous_subtype_val.subtype_mk _)
  have hc' : Continuous (fun q : Q =>
      (⟨(h.projection ⟨q, hQP q.property⟩ : G),
        (h.projection ⟨q, hQP q.property⟩).property,
        h.projection_mem_of_radical_le hQP hUQ q⟩ : ↥(M ⊓ Q))) :=
    (continuous_subtype_val.comp hc).subtype_mk _
  convert hc' using 1
  funext q
  exact Subtype.ext (h.restrict_projection hQP hUQ q)

/-- Continuous multiplication coordinates on the inherited intermediate subgroup. -/
def restrictedCoordinates [IsTopologicalGroup G] (hp : Continuous h.projection) :
    ↥(M ⊓ Q) × U ≃ₜ Q :=
  (h.restrict hQP hUQ).coordinates (h.continuous_restrict_projection hQP hUQ hp)

end Langlands.Aubert.General.IsSemidirectDecomposition

namespace Langlands.Aubert.General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

namespace IsSemidirectDecomposition

/-- The actual normalizer characters multiply when conjugation preserves
both factors of a continuous semidirect decomposition. -/
theorem closedNormalizerCharacter_eq_mul [SecondCountableTopology G]
    {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hp : Continuous h.projection)
    (hP : IsClosed (P : Set G)) (hM : IsClosed (M : Set G))
    (hU : IsClosed (U : Set G)) (g : G)
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hgM : g ∈ Subgroup.normalizer (M : Set G))
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    HaarModulus.closedNormalizerCharacter P hP ⟨g, hgP⟩ =
      HaarModulus.closedNormalizerCharacter M hM ⟨g, hgM⟩ *
        HaarModulus.closedNormalizerCharacter U hU ⟨g, hgU⟩ := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : MeasurableSpace P := borel P
  have : BorelSpace P := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  apply Units.ext
  change mulEquivHaarChar (HaarModulus.normalizerConj P ⟨g, hgP⟩) =
    mulEquivHaarChar (HaarModulus.normalizerConj M ⟨g, hgM⟩) *
      mulEquivHaarChar (HaarModulus.normalizerConj U ⟨g, hgU⟩)
  apply h.haarChar_eq_mul hp
  intro m u
  apply Subtype.ext
  change g * ((m : G) * (u : G)) * g⁻¹ =
    (g * (m : G) * g⁻¹) * (g * (u : G) * g⁻¹)
  simp only [mul_assoc, inv_mul_cancel_left]

end IsSemidirectDecomposition

/-- Reading a closed subgroup inside a closed ambient subgroup preserves
the Haar modulus of the same conjugation action. -/
theorem closedNormalizerCharacter_subgroupOf_of_mem
    (M W : Subgroup G) (hM : IsClosed (M : Set G))
    (hW : IsClosed (W : Set G)) (hWM : W ≤ M)
    (g : M) (hg : (g : G) ∈ Subgroup.normalizer (W : Set G))
    (hg' : g ∈ Subgroup.normalizer (W.subgroupOf M : Set M)) :
    letI := hM.locallyCompactSpace
    HaarModulus.closedNormalizerCharacter (W.subgroupOf M)
        (hW.preimage continuous_subtype_val) ⟨g, hg'⟩ =
      HaarModulus.closedNormalizerCharacter W hW ⟨g, hg⟩ := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace W := hW.locallyCompactSpace
  let : LocallyCompactSpace (W.subgroupOf M) :=
    (hW.preimage continuous_subtype_val).locallyCompactSpace
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let : MeasurableSpace (W.subgroupOf M) := borel (W.subgroupOf M)
  have : BorelSpace (W.subgroupOf M) := ⟨rfl⟩
  let e := subgroupOfContinuousEquiv hWM
  apply Units.ext
  change mulEquivHaarChar (HaarModulus.normalizerConj (W.subgroupOf M) ⟨g, hg'⟩) =
    mulEquivHaarChar (HaarModulus.normalizerConj W ⟨g, hg⟩)
  have he : HaarModulus.normalizerConj (W.subgroupOf M) ⟨g, hg'⟩ =
      (e.trans (HaarModulus.normalizerConj W ⟨g, hg⟩)).trans e.symm := by
    ext w
    rfl
  rw [he, mulEquivHaarChar_trans_symm]

end Langlands.Aubert.General
