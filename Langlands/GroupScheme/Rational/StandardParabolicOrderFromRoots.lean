import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.StandardParabolicOrderReduction

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Actual relative roots with nonnegative pairing against a cocharacter. -/
def nonnegativeRelativeRoots (zeta : cocharacterLattice T) : Set (characterLattice T) :=
  {α | α ∈ relativeRoots i ∧ 0 ≤ latticePairing T α zeta}

/-- Actual relative roots annihilated by a cocharacter. -/
def zeroRelativeRoots (zeta : cocharacterLattice T) : Set (characterLattice T) :=
  {α | α ∈ relativeRoots i ∧ latticePairing T α zeta = 0}

/-- Nested standard faces give covariant nonnegative and zero root supports,
 and contravariant positive root supports. -/
theorem IsStandardCocharacter.root_pairing_implications_of_subset
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J K : Set (characterLattice T)} {zeta eta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (heta : IsStandardCocharacter i ν K eta) (hJK : J ⊆ K)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    (0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta) ∧
    (latticePairing T α zeta = 0 → latticePairing T α eta = 0) ∧
    (0 < latticePairing T α eta → 0 < latticePairing T α zeta) := by
  have hzero : ∀ β ∈ positiveRelativeRoots i ν,
      latticePairing T β zeta = 0 → latticePairing T β eta = 0 := by
    intro β hβ hz
    exact (heta.pairing_eq_zero_iff_mem_closure i ν hβ).2
      (AddSubmonoid.closure_mono hJK ((hzeta.pairing_eq_zero_iff_mem_closure i ν hβ).1 hz))
  rcases lt_or_gt_of_ne (hν α hα) with hnegative | hpositive
  · have hpos : -α ∈ positiveRelativeRoots i ν :=
      ⟨hneg α hα, by simpa using neg_pos.mpr hnegative⟩
    have hz : latticePairing T α zeta ≤ 0 := by
      simpa using hzeta.pairing_nonneg_of_positive i ν hpos
    have he : latticePairing T α eta ≤ 0 := by
      simpa using heta.pairing_nonneg_of_positive i ν hpos
    have hzero' : latticePairing T α zeta = 0 → latticePairing T α eta = 0 := by
      intro hz'
      have hnz : latticePairing T (-α) zeta = 0 := by simpa using hz'
      simpa using hzero (-α) hpos hnz
    exact ⟨by omega, hzero', by omega⟩
  · have hpos : α ∈ positiveRelativeRoots i ν := ⟨hα, hpositive⟩
    refine ⟨fun _ => heta.pairing_nonneg_of_positive i ν hpos, hzero α hpos, ?_⟩
    intro he
    apply (hzeta.pairing_pos_iff_not_mem_closure i ν hpos).2
    intro hclosure
    exact (heta.pairing_pos_iff_not_mem_closure i ν hpos).1 he
      (AddSubmonoid.closure_mono hJK hclosure)

/-- Inclusions between the nonnegative, zero, and positive actual-root supports
 of cocharacters standard for nested faces. -/
theorem IsStandardCocharacter.root_supports_of_subset
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J K : Set (characterLattice T)} {zeta eta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta)
    (heta : IsStandardCocharacter i ν K eta) (hJK : J ⊆ K) :
    (nonnegativeRelativeRoots i zeta ⊆ nonnegativeRelativeRoots i eta) ∧
    (zeroRelativeRoots i zeta ⊆ zeroRelativeRoots i eta) ∧
    (positiveRelativeRoots i eta ⊆ positiveRelativeRoots i zeta) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    exact ⟨hα.1,
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta hJK hα.1).1 hα.2⟩
  · intro α hα
    exact ⟨hα.1,
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta hJK hα.1).2.1 hα.2⟩
  · intro α hα
    exact ⟨hα.1,
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta hJK hα.1).2.2 hα.2⟩

/-- The standard-parabolic order assertions follow from standard-cocharacter
 existence and all-cocharacter comparisons by actual root signs.
 All subgroup comparisons here are comparisons on every test scheme. -/
theorem standardParabolic_order_of_root_comparison
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hexists : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
        ∀ α ∈ relativeRoots i,
          0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta)
    (hunipotent : ∀ zeta eta : cocharacterLattice T,
      (∀ α ∈ relativeRoots i,
        0 < latticePairing T α zeta → 0 < latticePairing T α eta) →
      Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    (∀ J K : Set (characterLattice T),
      J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
        (J ⊆ K ↔ standardParabolic i ν J ≤ standardParabolic i ν K) ∧
        (J ⊆ K → standardLevi i ν J ≤ standardLevi i ν K ∧
          standardUnipotent i ν K ≤ standardUnipotent i ν J)) ∧
    Function.Injective (fun J : {J : Set (characterLattice T) //
      J ⊆ simpleRelativeRoots i ν} => standardParabolic i ν J.1) := by
  have hrealize : ∀ J : Set (characterLattice T), ∀ zeta,
      IsStandardCocharacter i ν J zeta →
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤ standardParabolic i ν J := by
    intro J zeta hzeta U g hg
    rw [mem_standardParabolic]
    intro eta heta
    have hle := (hparabolic zeta eta).2 (fun α hα hnonneg =>
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta (Set.Subset.refl J) hα).1
        hnonneg)
    exact hle U hg
  have hmono : ∀ J K : Set (characterLattice T),
      J ⊆ simpleRelativeRoots i ν → J ⊆ K →
      standardParabolic i ν J ≤ standardParabolic i ν K := by
    intro J K hJ hJK
    obtain ⟨zeta, hzeta⟩ := hexists J hJ
    intro U g hg
    rw [mem_standardParabolic]
    intro eta heta
    have hle := (hparabolic zeta eta).2 (fun α hα hnonneg =>
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta hJK hα).1 hnonneg)
    exact hle U (standardParabolic_le_dynamicParabolic i ν hzeta U hg)
  have hreflect : ∀ J K : Set (characterLattice T),
      J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
      standardParabolic i ν J ≤ standardParabolic i ν K → J ⊆ K := by
    intro J K hJ hK hle
    obtain ⟨zeta, hzeta⟩ := hexists J hJ
    obtain ⟨eta, heta⟩ := hexists K hK
    have hdynamic := (hrealize J zeta hzeta).trans
      (hle.trans (standardParabolic_le_dynamicParabolic i ν heta))
    intro α hα
    by_contra hαK
    have hαroot : α ∈ relativeRoots i := (hJ hα).1.1
    have hz : latticePairing T (-α) zeta = 0 := by
      simpa using hzeta.2.1 α hα
    have hn := (hparabolic zeta eta).1 hdynamic (-α) (hneg α hαroot) (by omega)
    have hp := heta.2.2 α (hJ hα) hαK
    simp only [map_neg, LinearMap.neg_apply] at hn
    omega
  have hanti : ∀ J K : Set (characterLattice T),
      K ⊆ simpleRelativeRoots i ν → J ⊆ K →
      standardUnipotent i ν K ≤ standardUnipotent i ν J := by
    intro J K hK hJK
    obtain ⟨eta, heta⟩ := hexists K hK
    intro U g hg
    rw [mem_standardUnipotent]
    intro zeta hzeta
    have hle := hunipotent eta zeta (fun α hα hpos =>
      (hzeta.root_pairing_implications_of_subset i ν hν hneg heta hJK hα).2.2 hpos)
    exact hle U (standardUnipotent_le_dynamicUnipotent i ν heta U hg)
  refine ⟨?_, ?_⟩
  · intro J K hJ hK
    exact ⟨⟨hmono J K hJ, hreflect J K hJ hK⟩, fun hJK =>
      ⟨standardLevi_mono_of_exists i ν hJK (hexists J hJ), hanti J K hK hJK⟩⟩
  · intro J K h
    apply Subtype.ext
    exact Set.Subset.antisymm
      (hreflect J.1 K.1 J.2 K.2 (le_of_eq h))
      (hreflect K.1 J.1 K.2 J.2 (le_of_eq h.symm))

end Langlands.GroupScheme
