import Langlands.Representation.Aubert.General.Parabolic
import Langlands.HarmonicAnalysis.HaarConjugacy

/-! # Actual Haar normalization inside a closed ambient subgroup -/

noncomputable section

namespace Langlands.Aubert.General

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
  {M U L : Subgroup G}

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Forget the intermediate ambient subgroup in an element normalizing
`U.subgroupOf M`. Containment `U ≤ M` ensures that it normalizes all of `U`. -/
def subgroupOfNormalizerMap (hUM : U ≤ M) :
    Subgroup.normalizer (U.subgroupOf M : Set M) →*
      Subgroup.normalizer (U : Set G) where
  toFun n := ⟨((n : M) : G), by
    have hn : (n : M) ∈ (Subgroup.normalizer (U : Set G)).subgroupOf M := by
      rw [Subgroup.subgroupOf_normalizer_eq hUM]
      exact n.2
    exact hn⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
@[simp]
theorem subgroupOfNormalizerMap_apply (hUM : U ≤ M)
    (n : Subgroup.normalizer (U.subgroupOf M : Set M)) :
    (subgroupOfNormalizerMap hUM n : G) = ((n : M) : G) := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- The normalizer map is continuous for the induced subgroup topologies. -/
theorem continuous_subgroupOfNormalizerMap (hUM : U ≤ M) :
    Continuous (subgroupOfNormalizerMap hUM) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Restricting two subgroups to an ambient subgroup preserves normalization. -/
theorem normalizes_subgroupOf (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    L.subgroupOf M ≤ Subgroup.normalizer (U.subgroupOf M : Set M) :=
  (Subgroup.comap_mono hLU).trans (Subgroup.le_normalizer_comap (H := U) M.subtype)

variable (hM : IsClosed (M : Set G))

/-- The modulus of the actual radical is unchanged when the radical is viewed
inside a closed ambient subgroup containing it. -/
theorem closedNormalizerCharacter_subgroupOf (hU : IsClosed (U : Set G))
    (hUM : U ≤ M) (g : M) (hg : (g : G) ∈ Subgroup.normalizer (U : Set G)) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedNormalizerCharacter (U.subgroupOf M)
        (hU.preimage continuous_subtype_val)
        ⟨g, Subgroup.le_normalizer_comap (H := U) M.subtype hg⟩ =
      HaarModulus.closedNormalizerCharacter U hU ⟨g, hg⟩ := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace (U.subgroupOf M) :=
    (hU.preimage continuous_subtype_val).locallyCompactSpace
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace (U.subgroupOf M) := borel (U.subgroupOf M)
  let : BorelSpace (U.subgroupOf M) := ⟨rfl⟩
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar
      (HaarModulus.normalizerConj (U.subgroupOf M)
        ⟨g, Subgroup.le_normalizer_comap (H := U) M.subtype hg⟩) =
    MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U ⟨g, hg⟩)
  apply Geometric.haarChar_eq_of_conjugacy (subgroupOfContinuousEquiv hUM)
  intro u
  rfl

/-- The normalizer character inside `M` is the ambient actual Haar character
pulled back through the continuous normalizer map. -/
theorem closedNormalizerCharacter_subgroupOf_comp (hU : IsClosed (U : Set G))
    (hUM : U ≤ M) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedNormalizerCharacter (U.subgroupOf M)
        (hU.preimage continuous_subtype_val) =
      (HaarModulus.closedNormalizerCharacter U hU).comp
        (subgroupOfNormalizerMap hUM) := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  apply MonoidHom.ext
  intro n
  exact closedNormalizerCharacter_subgroupOf hM hU hUM (n : M)
    (subgroupOfNormalizerMap hUM n).2

/-- The restricted actual modulus agrees through the continuous identification
of the acting subgroup with its copy inside the ambient subgroup. -/
theorem closedRestrictCharacter_subgroupOf (hU : IsClosed (U : Set G))
    (hUM : U ≤ M) (hLM : L ≤ M)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : L.subgroupOf M) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedRestrictCharacter (U.subgroupOf M)
        (hU.preimage continuous_subtype_val) (L.subgroupOf M)
        (normalizes_subgroupOf hLU) l =
      HaarModulus.closedRestrictCharacter U hU L hLU
        (subgroupOfContinuousEquiv hLM l) := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  exact closedNormalizerCharacter_subgroupOf hM hU hUM (l : M) (hLU l.2)

/-- The positive complex half-modulus agrees inside the closed ambient
subgroup, with its canonical positive square root retained. -/
theorem closedHalfCharacter_subgroupOf (hU : IsClosed (U : Set G))
    (hUM : U ≤ M) (hLM : L ≤ M)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : L.subgroupOf M) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedHalfCharacter (U.subgroupOf M)
        (hU.preimage continuous_subtype_val) (L.subgroupOf M)
        (normalizes_subgroupOf hLU) l =
      HaarModulus.closedHalfCharacter U hU L hLU
        (subgroupOfContinuousEquiv hLM l) := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  unfold HaarModulus.closedHalfCharacter Jacquet.complexCharacter
    Jacquet.positiveHalfCharacter
  simp only [MonoidHom.comp_apply]
  rw [closedRestrictCharacter_subgroupOf hM hU hUM hLM hLU l]

/-- The inverse half-modulus used in Jacquet normalization agrees inside the
closed ambient subgroup. -/
theorem closedInverseHalfCharacter_subgroupOf (hU : IsClosed (U : Set G))
    (hUM : U ≤ M) (hLM : L ≤ M)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : L.subgroupOf M) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedInverseHalfCharacter (U.subgroupOf M)
        (hU.preimage continuous_subtype_val) (L.subgroupOf M)
        (normalizes_subgroupOf hLU) l =
      HaarModulus.closedInverseHalfCharacter U hU L hLU
        (subgroupOfContinuousEquiv hLM l) := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  unfold HaarModulus.closedInverseHalfCharacter Jacquet.inverseHalfCharacter
    Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
  rw [closedRestrictCharacter_subgroupOf hM hU hUM hLM hLU l]

end Langlands.Aubert.General
