import Langlands.GroupScheme.Rational.StandardLeviTwistedRootSupport

/-! # Vanishing roots of twisted standard-Levi intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- On positive roots, simultaneous vanishing on the right face and the
transported left face is vanishing on the intrinsic intersection face. -/
theorem IsRelativeWeylCoxeterRealization.twisted_pairing_eq_zero_iff_of_positive
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)}
    {ζI ζJ ζK : cocharacterLattice T}
    (hI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (hK : IsStandardCocharacter i ν
      (rootSet i ν (intersectionSubset cs I J w)) ζK)
    {α : characterLattice T} (hα : α ∈ positiveRelativeRoots i ν) :
    (latticePairing T α ζJ = 0 ∧
      latticePairing T (schemeWeylCharacterAction i w α) ζI = 0) ↔
        latticePairing T α ζK = 0 := by
  constructor
  · rintro ⟨hzeroJ, hzeroI⟩
    have hαJ := (hJ.pairing_eq_zero_iff_mem_closure i ν hα).mp hzeroJ
    have hαK := (h.mem_closure_intersectionSubset_iff hν hI hw hαJ).mpr hzeroI
    exact hK.pairing_eq_zero_of_mem_closure i ν hαK
  · intro hzeroK
    have hαK := (hK.pairing_eq_zero_iff_mem_closure i ν hα).mp hzeroK
    have hsub : rootSet i ν (intersectionSubset cs I J w) ⊆ rootSet i ν J := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, intersectionSubset_subset cs I J w ha, rfl⟩
    have hαJ := AddSubmonoid.closure_mono hsub hαK
    exact ⟨hJ.pairing_eq_zero_of_mem_closure i ν hαJ,
      (h.mem_closure_intersectionSubset_iff hν hI hw hαJ).mp hαK⟩

/-- With explicit negation stability, the twisted-face vanishing criterion
holds on every actual relative root. -/
theorem IsRelativeWeylCoxeterRealization.twisted_pairing_eq_zero_iff_of_root
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {I J : Finset (SimpleRoot i ν)}
    {ζI ζJ ζK : cocharacterLattice T}
    (hI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (hK : IsStandardCocharacter i ν
      (rootSet i ν (intersectionSubset cs I J w)) ζK)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    (latticePairing T α ζJ = 0 ∧
      latticePairing T (schemeWeylCharacterAction i w α) ζI = 0) ↔
        latticePairing T α ζK = 0 := by
  rcases lt_or_gt_of_ne (hν α hα) with hnegative | hpositive
  · have hpos : -α ∈ positiveRelativeRoots i ν :=
      ⟨hneg α hα, by simpa using neg_pos.mpr hnegative⟩
    simpa using h.twisted_pairing_eq_zero_iff_of_positive hν hI hJ hw hK hpos
  · exact h.twisted_pairing_eq_zero_iff_of_positive hν hI hJ hw hK ⟨hα, hpositive⟩

/-- The actual relative roots vanishing on a right cocharacter and, after
transport, on a left cocharacter. -/
def twistedStandardRelativeRootZeroSupport
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (w : relativeWeylGroup i) (ζJ ζI : cocharacterLattice T) :
    Set (characterLattice T) :=
  {α | α ∈ relativeRoots i ∧ latticePairing T α ζJ = 0 ∧
    latticePairing T (schemeWeylCharacterAction i w α) ζI = 0}

/-- The simultaneous vanishing-root support equals the vanishing-root support
of the intrinsic intersection face. -/
theorem IsRelativeWeylCoxeterRealization.twistedStandardRelativeRootZeroSupport_eq
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {I J : Finset (SimpleRoot i ν)}
    {ζI ζJ ζK : cocharacterLattice T}
    (hI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (hK : IsStandardCocharacter i ν
      (rootSet i ν (intersectionSubset cs I J w)) ζK) :
    twistedStandardRelativeRootZeroSupport i w ζJ ζI =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ζK = 0} := by
  ext α
  change (α ∈ relativeRoots i ∧ _) ↔ (α ∈ relativeRoots i ∧ _)
  exact and_congr_right fun hα =>
    h.twisted_pairing_eq_zero_iff_of_root hν hneg hI hJ hw hK hα

/-- The vanishing-root criterion holds for every normalizer lift of the given
minimal representative, with its actual forward character action. -/
theorem IsRelativeWeylCoxeterRealization.twisted_pairing_eq_zero_iff_of_lift
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {I J : Finset (SimpleRoot i ν)}
    {ζI ζJ ζK : cocharacterLattice T}
    (hI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (hK : IsStandardCocharacter i ν
      (rootSet i ν (intersectionSubset cs I J w)) ζK)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    (latticePairing T α ζJ = 0 ∧
      latticePairing T (weylAction i n α) ζI = 0) ↔
        latticePairing T α ζK = 0 := by
  have haction : schemeWeylCharacterAction i w = weylAction i n := by
    rw [← hn, schemeWeylCharacterAction_mk]
  simpa only [haction] using
    h.twisted_pairing_eq_zero_iff_of_root hν hneg hI hJ hw hK hα

end Langlands.GroupScheme
