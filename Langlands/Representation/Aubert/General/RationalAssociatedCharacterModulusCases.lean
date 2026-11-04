import Langlands.Representation.Aubert.General.RationalAssociatedCentralCharacterSigns
import Langlands.Representation.Aubert.General.RationalLatticeStrictExponentProof

/-! # Modulus cases for actual associated maximal Levi characters -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]

/-- A chosen omitted root and the real logarithmic modulus factor of an
actual maximal Levi character, with the original index retained. -/
structure MaximalLeviCentralCharacterLogData
    (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ) where
  omittedRoot : SimpleRoot i ν
  index_eq : I = Finset.univ.erase omittedRoot
  slope : ℝ
  factor : ∀ t : leviCentralTorusPoints i ν I,
    (leviCentralTorusCharacterLog i ν I χ t).toAdd =
      slope * ((Plancherel.fieldOrderUnits k
        (simpleRootPointValue i ν omittedRoot t)).toAdd : ℝ)

/-- A standard cocharacter for a maximal proper index gives a noncentral
negative torus test at the actual common uniformizer. -/
theorem standardCocharacterUniformizer_isNoncentralNegative
    (I : Finset (SimpleRoot i ν)) (hI : IsMaximalStandard I)
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν I) ζ}) :
    IsNoncentralNegativeTorusPoint i ν
      (Plancherel.RenardCartan.uniformizerSection T (.ofAdd ζ.val)) := by
  apply isNoncentralNegativeTorusPoint_uniformizerSection i ν ζ.val
  · intro β
    by_cases hβ : β ∈ I
    · exact le_of_eq (ζ.property.2.1 β.val
        ((val_mem_rootSet i ν I β).mpr hβ)).symm
    · exact le_of_lt (ζ.property.2.2 β.val β.property (by
        intro h
        exact hβ ((val_mem_rootSet i ν I β).mp h)))
  · obtain ⟨α, hα⟩ := hI
    refine ⟨α, ζ.property.2.2 α.val α.property ?_⟩
    intro h
    have hm := (val_mem_rootSet i ν I α).mp h
    rw [hα] at hm
    exact (Finset.mem_erase.mp hm).1 rfl

local instance associatedModulusAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

section Topology

variable [IsAffine T.X.left]
  [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  [Mono i.hom.hom.left]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)

/-- The rational structural data construct a logarithmic modulus factor for
every actual maximal index and every smooth character unitary on the ambient
center. The omitted root and real factor are chosen as actual data. -/
def maximalLeviCentralCharacterLogData
    (I : Finset (SimpleRoot i ν)) (hI : IsMaximalStandard I)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter _
        (center_le_standardLevi i ν hZ _) z) : ℂ)‖ = 1) :
    MaximalLeviCentralCharacterLogData i ν I χ :=
  Classical.choice (show Nonempty (MaximalLeviCentralCharacterLogData i ν I χ) from by
    obtain ⟨α, hI⟩ := hI
    subst I
    obtain ⟨slope, hslope⟩ := exists_leviCentralTorusCharacterLog_factor_of_rationalData
      i ν hN hZ cs hStandard hG hi hRoots hν hLength hIdent α χ hχ hχambient
    exact ⟨⟨α, rfl, slope, hslope⟩⟩)

include hN hZ cs hi hRoots hν hLength hIdent in
omit [IsAffine T.X.left] [IsTopologicalGroup (rationalPoints G)]
  [T2Space (rationalPoints G)] in
/-- Logarithmic modulus data give the three uniform modulus possibilities
on the literal central torus tests, for the original arbitrary maximal index. -/
theorem MaximalLeviCentralCharacterLogData.norm_trichotomy
    {I : Finset (SimpleRoot i ν)}
    {χ : Subgroup.center (levi i ν I) →* ℂˣ}
    (D : MaximalLeviCentralCharacterLogData i ν I χ) :
    (∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ z : ℂ)‖ < 1) ∨
    (∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → 1 < ‖(χ z : ℂ)‖) ∨
    (∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ z : ℂ)‖ = 1) := by
  rcases D with ⟨α, hI, slope, hslope⟩
  subst I
  have htmem (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) =
        t ≫ i.hom.hom) :
      t ∈ leviCentralTorusPoints i ν (Finset.univ.erase α) :=
    (mem_leviCentralTorusPoints_iff i ν _ t).mpr ⟨z, hz⟩
  have heq (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) =
        t ≫ i.hom.hom) :
      leviCentralTorusPointToCenter i ν _ ⟨t, htmem t z hz⟩ = z := by
    apply Subtype.ext
    apply Subtype.ext
    exact hz.symm
  have htest (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) =
        t ≫ i.hom.hom)
      (ht : IsNoncentralNegativeTorusPoint i ν t) :
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 :=
    (isNoncentralNegativeTorusPoint_iff_omittedRoot_lt i ν hN hZ cs
      hi.isSplitSubtorus.1 hRoots hν hLength hIdent α t (htmem t z hz)).mp ht
  rcases leviCentralTorusCharacter_norm_trichotomy_of_factor i ν α χ slope hslope with
    hpos | hneg | hzero
  · left
    intro t z hz ht
    simpa only [heq t z hz] using hpos ⟨t, htmem t z hz⟩ (htest t z hz ht)
  · right
    left
    intro t z hz ht
    simpa only [heq t z hz] using hneg ⟨t, htmem t z hz⟩ (htest t z hz ht)
  · right
    right
    intro t z hz
    simpa only [heq t z hz] using hzero ⟨t, htmem t z hz⟩

variable [Fintype (Weyl i)]
  (hConj : StandardLeviConjugationStatement.{u})
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)

include hStandard hRoots hIdent in
omit [IsAffine T.X.left] [T2Space (rationalPoints G)] in
set_option maxHeartbeats 800000 in
/-- Two actual associated full-center characters with factored logarithmic
moduli have a strict first case, a strict second case, or unit modulus on both
central tori. The inverse relation is supplied by the literal longest lift. -/
theorem associatedLeviCentralCharacters_norm_cases_of_logData
    (I : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs I)
    (χ₁ : Subgroup.center (levi i ν I) →* ℂˣ)
    (χ₂ : Subgroup.center (levi i ν (associatedSubset cs I)) →* ℂˣ)
    (D₁ : MaximalLeviCentralCharacterLogData i ν I χ₁)
    (D₂ : MaximalLeviCentralCharacterLogData i ν (associatedSubset cs I) χ₂)
    (hχ₂ : χ₂ = associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc I n hn χ₁) :
    (∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ₁ z : ℂ)‖ < 1) ∨
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (associatedSubset cs I))),
      ((z : levi i ν (associatedSubset cs I)) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ₂ z : ℂ)‖ < 1) ∨
    ((∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ₁ z : ℂ)‖ = 1) ∧
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (associatedSubset cs I))),
      ((z : levi i ν (associatedSubset cs I)) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ₂ z : ℂ)‖ = 1)) := by
  let ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν I) ζ} :=
    ⟨_, (hStandard k G hG T i hi ν hν _ (rootSet_subset i ν I)).1.choose_spec⟩
  let ξ := associatedOppositeStandardCocharacter i ν hN hZ cs hLength hSimple hMin
    hAssoc hi.isSplitSubtorus.1 hRoots hν I n hn ζ
  let hfinite := hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν
  let t₁ := Plancherel.RenardCartan.uniformizerSection T (.ofAdd ζ.val)
  let t₂ := Plancherel.RenardCartan.uniformizerSection T (.ofAdd ξ.val)
  let z₁ := standardCocharacterUniformizerCenter i ν hfinite I ζ
  let z₂ := standardCocharacterUniformizerCenter i ν hfinite (associatedSubset cs I) ξ
  have hz₁ : ((z₁ : levi i ν I) : rationalPoints G) = t₁ ≫ i.hom.hom := rfl
  have hz₂ : ((z₂ : levi i ν (associatedSubset cs I)) : rationalPoints G) =
      t₂ ≫ i.hom.hom := rfl
  have ht₁ : IsNoncentralNegativeTorusPoint i ν t₁ :=
    standardCocharacterUniformizer_isNoncentralNegative i ν I
      ⟨D₁.omittedRoot, D₁.index_eq⟩ ζ
  have ht₂ : IsNoncentralNegativeTorusPoint i ν t₂ :=
    standardCocharacterUniformizer_isNoncentralNegative i ν _
      ⟨D₂.omittedRoot, D₂.index_eq⟩ ξ
  have hvalue : χ₂ z₂ = (χ₁ z₁)⁻¹ := by
    rw [hχ₂]
    exact associatedLeviCentralCharacter_standardUniformizer i ν hG hi hν hConj
      hN hZ cs hLength hSimple hMin hAssoc hRoots I n hn ζ χ₁
  have hnorm : ‖(χ₂ z₂ : ℂ)‖ = ‖(χ₁ z₁ : ℂ)‖⁻¹ := by
    rw [hvalue, Units.val_inv_eq_inv_val, norm_inv]
  rcases MaximalLeviCentralCharacterLogData.norm_trichotomy i ν hN hZ cs hi hRoots hν
    hLength hIdent D₁ with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · rcases MaximalLeviCentralCharacterLogData.norm_trichotomy i ν hN hZ cs hi hRoots hν
      hLength hIdent D₂ with h₂ | h₂ | h₂
    · exact Or.inr (Or.inl h₂)
    · have hlt : ‖(χ₂ z₂ : ℂ)‖ < 1 := by
        rw [hnorm]
        exact inv_lt_one_of_one_lt₀ (h₁ t₁ z₁ hz₁ ht₁)
      exact (not_lt_of_gt (h₂ t₂ z₂ hz₂ ht₂) hlt).elim
    · have hlt : ‖(χ₂ z₂ : ℂ)‖ < 1 := by
        rw [hnorm]
        exact inv_lt_one_of_one_lt₀ (h₁ t₁ z₁ hz₁ ht₁)
      exact (ne_of_lt hlt (h₂ t₂ z₂ hz₂)).elim
  · have heq : ‖(χ₂ z₂ : ℂ)‖ = 1 := by
      rw [hnorm, h₁ t₁ z₁ hz₁, inv_one]
    rcases MaximalLeviCentralCharacterLogData.norm_trichotomy i ν hN hZ cs hi hRoots hν
      hLength hIdent D₂ with h₂ | h₂ | h₂
    · exact (ne_of_lt (h₂ t₂ z₂ hz₂ ht₂) heq).elim
    · exact (ne_of_gt (h₂ t₂ z₂ hz₂ ht₂) heq).elim
    · exact Or.inr (Or.inr ⟨h₁, h₂⟩)

include hStandard hRoots hIdent in
set_option maxHeartbeats 800000 in
/-- Smooth actual full-center characters, unitary on the ambient center and
related by the specified longest conjugation, satisfy the paired modulus
alternatives without an additional sign or factorization premise. -/
theorem associatedLeviCentralCharacters_norm_cases_of_rationalData
    (I : Finset (SimpleRoot i ν)) (hI : IsMaximalStandard I)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs I)
    (χ₁ : Subgroup.center (levi i ν I) →* ℂˣ)
    (χ₂ : Subgroup.center (levi i ν (associatedSubset cs I)) →* ℂˣ)
    (hχ₁open : IsOpen (χ₁.ker : Set (Subgroup.center (levi i ν I))))
    (hχ₂open : IsOpen (χ₂.ker :
      Set (Subgroup.center (levi i ν (associatedSubset cs I)))))
    (hχ₁ambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ₁ (ambientCenterToLeviCenter _
        (center_le_standardLevi i ν hZ _) z) : ℂ)‖ = 1)
    (hχ₂ambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ₂ (ambientCenterToLeviCenter _
        (center_le_standardLevi i ν hZ _) z) : ℂ)‖ = 1)
    (hχ₂ : χ₂ = associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc I n hn χ₁) :
    (∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ₁ z : ℂ)‖ < 1) ∨
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (associatedSubset cs I))),
      ((z : levi i ν (associatedSubset cs I)) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ₂ z : ℂ)‖ < 1) ∨
    ((∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ₁ z : ℂ)‖ = 1) ∧
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (associatedSubset cs I))),
      ((z : levi i ν (associatedSubset cs I)) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ₂ z : ℂ)‖ = 1)) := by
  have hJ : IsMaximalStandard (associatedSubset cs I) := by
    obtain ⟨α, hα⟩ := hI
    have hIcard : I.card = (Finset.univ : Finset (SimpleRoot i ν)).card - 1 := by
      rw [hα, Finset.card_erase_of_mem (Finset.mem_univ α)]
    have hcard := (hAssoc I).2.1.trans hIcard
    have hproper : associatedSubset cs I ≠ Finset.univ := by
      intro heq
      rw [heq, Finset.card_univ] at hcard
      have hpos : 0 < Fintype.card (SimpleRoot i ν) :=
        Fintype.card_pos_iff.mpr ⟨α⟩
      omega
    obtain ⟨β, hβ⟩ : ∃ β : SimpleRoot i ν, β ∉ associatedSubset cs I := by
      by_contra h
      push Not at h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    refine ⟨β, Finset.eq_of_subset_of_card_le
      (Finset.subset_erase.mpr ⟨Finset.subset_univ _, hβ⟩) ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ β)]
    exact hcard.ge
  exact associatedLeviCentralCharacters_norm_cases_of_logData i ν hN hZ cs hStandard
    hG hi hRoots hν hLength hIdent hConj hSimple hMin hAssoc I n hn χ₁ χ₂
    (maximalLeviCentralCharacterLogData i ν hN hZ cs hStandard hG hi hRoots hν
      hLength hIdent I hI χ₁ hχ₁open hχ₁ambient)
    (maximalLeviCentralCharacterLogData i ν hN hZ cs hStandard hG hi hRoots hν
      hLength hIdent _ hJ χ₂ hχ₂open hχ₂ambient) hχ₂

end Topology

end Langlands.Aubert.General.RationalPointFamily
