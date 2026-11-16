import Langlands.GroupScheme.Rational.StandardRootSubsetWeyl
import Langlands.GroupScheme.Rational.RenardIndivisibleRootComparison
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # Pairing loci needed by the standard root-subset group proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.StandardRootSubsetPairing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {R : Set (characterLattice T)} {ν : cocharacterLattice T}
  {Θ : Set (characterLattice T)} {ζ : cocharacterLattice T}

omit [Mono i.hom.hom.left] in
theorem subset_relativeRoots (hR : IsRelativeRootAmbient i R) :
    R ⊆ relativeRoots i := by
  rcases hR with rfl | rfl
  · exact subset_rfl
  · exact fun _ h => h.1

theorem neg_mem (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ∈ R) : -a ∈ R := by
  rcases hR with rfl | rfl
  · exact hroot.neg_mem_relativeRoots i hT ha
  · refine ⟨hroot.neg_mem_relativeRoots i hT ha.1, ?_⟩
    intro b hb n hn heq
    apply ha.2 (-b) (hroot.neg_mem_relativeRoots i hT hb) n hn
    simp only [smul_neg, heq, neg_neg]

theorem simple_comparison (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) :
    {a | a ∈ positiveRootSubset R ν ∧
      ¬ ∃ b ∈ positiveRootSubset R ν, ∃ c ∈ positiveRootSubset R ν, a = b + c} =
        simpleRelativeRoots i ν := by
  rcases hR with rfl | rfl
  · rfl
  · exact hroot.indivisiblePositiveRootComparison hT hν

/-- Induction in either ambient root set retains membership of the sum in that set. -/
theorem positive_induction (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) {P : characterLattice T → Prop}
    (hsimple : ∀ a ∈ simpleRelativeRoots i ν, P a)
    (hadd : ∀ a ∈ positiveRootSubset R ν, ∀ b ∈ positiveRootSubset R ν,
      a + b ∈ R → P a → P b → P (a + b))
    {a : characterLattice T} (ha : a ∈ positiveRootSubset R ν) : P a := by
  generalize hn : (latticePairing T a ν).toNat = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hs : a ∈ simpleRelativeRoots i ν
    · exact hsimple a hs
    · have hdecomp : ∃ b ∈ positiveRootSubset R ν,
          ∃ c ∈ positiveRootSubset R ν, a = b + c := by
        by_contra hnone
        apply hs
        rw [← simple_comparison hR hroot hT hν]
        exact ⟨ha, hnone⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := hdecomp
      have hsum : latticePairing T (b + c) ν =
          latticePairing T b ν + latticePairing T c ν := by simp
      have hb_lt : (latticePairing T b ν).toNat < n := by
        have := ha.2
        have := hb.2
        have := hc.2
        omega
      have hc_lt : (latticePairing T c ν).toNat < n := by
        have := ha.2
        have := hb.2
        have := hc.2
        omega
      exact hadd b hb c hc ha.1 (ih _ hb_lt hb rfl) (ih _ hc_lt hc rfl)

/-- Every closed ambient root subset containing both signs of Θ contains all
roots on which a standard cocharacter for Θ vanishes. -/
theorem zero_locus_subset (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) (hζ : IsStandardCocharacter i ν Θ ζ)
    {X : Set (characterLattice T)} (hX : IsClosedRootSubset R X)
    (hΘX : Θ ⊆ X) (hnegΘX : ∀ a ∈ Θ, -a ∈ X) :
    {a | a ∈ R ∧ latticePairing T a ζ = 0} ⊆ X := by
  have hpositive {a : characterLattice T} (ha : a ∈ positiveRootSubset R ν) :
      latticePairing T a ζ = 0 → a ∈ X ∧ -a ∈ X := by
    apply positive_induction hR hroot hT hν (ha := ha)
    · intro b hb hzero
      have hbΘ : b ∈ Θ := by
        by_contra hnot
        have := hζ.2.2 b hb hnot
        omega
      exact ⟨hΘX hbΘ, hnegΘX b hbΘ⟩
    · intro b hb c hc hsum hbind hcind hzero
      have hbnonneg := hζ.pairing_nonneg_of_positive i ν
        ⟨subset_relativeRoots hR hb.1, hb.2⟩
      have hcnonneg := hζ.pairing_nonneg_of_positive i ν
        ⟨subset_relativeRoots hR hc.1, hc.2⟩
      have heq : latticePairing T b ζ + latticePairing T c ζ = 0 := by
        simpa using hzero
      obtain ⟨hbX, hnbX⟩ := hbind (by omega)
      obtain ⟨hcX, hncX⟩ := hcind (by omega)
      refine ⟨hX.2 b hbX c hcX hsum, ?_⟩
      simpa only [neg_add] using
        hX.2 (-b) hnbX (-c) hncX (by
          simpa only [neg_add] using neg_mem hR hroot hT hsum)
  rintro a ⟨ha, hzero⟩
  rcases lt_or_gt_of_ne (hν a (subset_relativeRoots hR ha)) with hneg | hpos
  · have hna : -a ∈ positiveRootSubset R ν :=
      ⟨neg_mem hR hroot hT ha, by simpa using neg_pos.mpr hneg⟩
    have hz : latticePairing T (-a) ζ = 0 := by simp [hzero]
    simpa only [neg_neg] using (hpositive hna hz).2
  · exact (hpositive ⟨ha, hpos⟩ hzero).1

/-- The two generated root sets needed for identifying their groups are the
weak and zero pairing loci of any standard cocharacter. -/
theorem standard_sets_pairing (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) (hΘ : Θ ⊆ simpleRelativeRoots i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ) :
    standardParabolicRootSubset R ν Θ = {a | a ∈ R ∧ 0 ≤ latticePairing T a ζ} ∧
      standardLeviRootSubset R Θ = {a | a ∈ R ∧ latticePairing T a ζ = 0} := by
  have hΘR : Θ ⊆ R := by
    intro a ha
    have hsimple := hΘ ha
    rw [← simple_comparison hR hroot hT hν] at hsimple
    exact hsimple.1.1
  have hseedM : Θ ∪ {a | -a ∈ Θ} ⊆ R := by
    rintro a (ha | ha)
    · exact hΘR ha
    · simpa only [neg_neg] using neg_mem hR hroot hT (hΘR ha)
  have hMclosed : IsClosedRootSubset R (standardLeviRootSubset R Θ) :=
    isClosedRootSubset_rootClosure hseedM
  have hM : standardLeviRootSubset R Θ =
      {a | a ∈ R ∧ latticePairing T a ζ = 0} := by
    apply Set.Subset.antisymm
    · intro a ha
      exact ⟨hMclosed.1 ha,
        StandardRootSubsetWeyl.pairing_eq_zero_of_mem_levi
          (fun _ hb => neg_mem hR hroot hT hb) hΘR hζ ha⟩
    · apply zero_locus_subset hR hroot hT hν hζ hMclosed
      · exact fun _ ha => subset_rootClosure _ (Or.inl ha)
      · intro a ha
        exact subset_rootClosure _ (Or.inr (by
          simpa only [Set.mem_ofPred_eq, neg_neg] using ha))
  refine ⟨?_, hM⟩
  have hnonneg : IsClosedRootSubset R
      {a | a ∈ R ∧ 0 ≤ latticePairing T a ζ} := by
    refine ⟨fun _ ha => ha.1, ?_⟩
    intro a ha b hb hsum
    exact ⟨hsum, by simpa using add_nonneg ha.2 hb.2⟩
  have hPle : standardParabolicRootSubset R ν Θ ⊆
      {a | a ∈ R ∧ 0 ≤ latticePairing T a ζ} := by
    apply rootClosure_subset hnonneg
    rintro a (ha | ha)
    · exact ⟨ha.1, hζ.pairing_nonneg_of_positive i ν
        ⟨subset_relativeRoots hR ha.1, ha.2⟩⟩
    · refine ⟨by simpa only [neg_neg] using neg_mem hR hroot hT (hΘR ha), ?_⟩
      have hz := hζ.2.1 (-a) ha
      have hz' : latticePairing T a ζ = 0 := by simpa using hz
      exact le_of_eq hz'.symm
  have hPclosed : IsClosedRootSubset R (standardParabolicRootSubset R ν Θ) :=
    isClosedRootSubset_rootClosure (fun _ ha => (hPle (subset_rootClosure _ ha)).1)
  have hMleP : standardLeviRootSubset R Θ ⊆ standardParabolicRootSubset R ν Θ := by
    apply rootClosure_subset hPclosed
    rintro a (ha | ha)
    · exact subset_rootClosure _ (Or.inl ⟨hΘR ha, (hΘ ha).1.2⟩)
    · exact subset_rootClosure _ (Or.inr ha)
  apply Set.Subset.antisymm hPle
  rintro a ⟨ha, hnonneg⟩
  rcases lt_or_gt_of_ne (hν a (subset_relativeRoots hR ha)) with hneg | hpos
  · have hna : -a ∈ positiveRelativeRoots i ν :=
      ⟨subset_relativeRoots hR (neg_mem hR hroot hT ha),
        by simpa using neg_pos.mpr hneg⟩
    have hna_nonneg := hζ.pairing_nonneg_of_positive i ν hna
    have hzero : latticePairing T a ζ = 0 := by
      have : 0 ≤ -latticePairing T a ζ := by simpa using hna_nonneg
      omega
    exact hMleP (hM.symm ▸ ⟨ha, hzero⟩)
  · exact subset_rootClosure _ (Or.inl ⟨ha, hpos⟩)

end Langlands.GroupScheme.StandardRootSubsetPairing
