import Langlands.GroupScheme.Rational.RootSubsetAmbient
import Langlands.GroupScheme.Rational.RenardIndivisibleRootComparison
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Mathlib.Tactic.Linarith

/-! # Standard root closures in either relative-root ambient set -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {R : Set (characterLattice T)} {ν : cocharacterLattice T}

namespace IsRelativeRootAmbient

theorem neg_mem (hR : IsRelativeRootAmbient i R) (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ∈ R) : -α ∈ R := by
  rcases hR with rfl | rfl
  · exact hroot.neg_mem_relativeRoots i hT hα
  · refine ⟨hroot.neg_mem_relativeRoots i hT hα.1, ?_⟩
    intro β hβ n hn heq
    apply hα.2 (-β) (hroot.neg_mem_relativeRoots i hT hβ) n hn
    simpa using congrArg Neg.neg heq

theorem simple_subset (hR : IsRelativeRootAmbient i R) (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν) :
    simpleRelativeRoots i ν ⊆ R := by
  rcases hR with rfl | rfl
  · exact fun _ h => h.1.1
  · intro α hα
    have hcomp := hroot.indivisiblePositiveRootComparison hT hν
    change {α | α ∈ RelativeRoot.indivisiblePositiveRoots i ν ∧
      ¬ ∃ β ∈ RelativeRoot.indivisiblePositiveRoots i ν,
        ∃ γ ∈ RelativeRoot.indivisiblePositiveRoots i ν, α = β + γ} = _ at hcomp
    exact ((Set.ext_iff.mp hcomp α).mpr hα).1.1

/-- Positive-root induction with every intermediate sum in the chosen ambient set. -/
theorem positive_induction (hR : IsRelativeRootAmbient i R) (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    {P : characterLattice T → Prop}
    (hsimple : ∀ α ∈ simpleRelativeRoots i ν, P α)
    (hadd : ∀ α ∈ positiveRootSubset R ν, ∀ β ∈ positiveRootSubset R ν,
      α + β ∈ R → P α → P β → P (α + β))
    {α : characterLattice T} (hα : α ∈ positiveRootSubset R ν) : P α := by
  have hbase : {α | α ∈ positiveRootSubset R ν ∧
      ¬ ∃ β ∈ positiveRootSubset R ν,
        ∃ γ ∈ positiveRootSubset R ν, α = β + γ} = simpleRelativeRoots i ν := by
    rcases hR with rfl | rfl
    · rfl
    · exact hroot.indivisiblePositiveRootComparison hT hν
  generalize hn : (latticePairing T α ν).toNat = n
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases hs : α ∈ simpleRelativeRoots i ν
    · exact hsimple α hs
    · have hdecomp : ∃ β ∈ positiveRootSubset R ν,
          ∃ γ ∈ positiveRootSubset R ν, α = β + γ := by
        by_contra h
        exact hs ((Set.ext_iff.mp hbase α).mp ⟨hα, h⟩)
      obtain ⟨β, hβ, γ, hγ, rfl⟩ := hdecomp
      have hsum : latticePairing T (β + γ) ν =
          latticePairing T β ν + latticePairing T γ ν := by simp
      have hb : (latticePairing T β ν).toNat < n := by
        have := hα.2
        have := hβ.2
        have := hγ.2
        omega
      have hc : (latticePairing T γ ν).toNat < n := by
        have := hα.2
        have := hβ.2
        have := hγ.2
        omega
      exact hadd β hβ γ hγ hα.1 (ih _ hb hβ rfl) (ih _ hc hγ rfl)

end IsRelativeRootAmbient

namespace StandardRootTriple

variable {Θ : Set (characterLattice T)} {ζ : cocharacterLattice T}

theorem isClosed_nonneg : IsClosedRootSubset R {α | α ∈ R ∧ 0 ≤ latticePairing T α ζ} := by
  refine ⟨fun _ h => h.1, fun α hα β hβ hsum => ⟨hsum, ?_⟩⟩
  simpa using add_nonneg hα.2 hβ.2

theorem isClosed_zero : IsClosedRootSubset R {α | α ∈ R ∧ latticePairing T α ζ = 0} := by
  refine ⟨fun _ h => h.1, fun α hα β hβ hsum => ⟨hsum, ?_⟩⟩
  simp [hα.2, hβ.2]

/-- A closed set containing both signs of Θ contains every root killed by ζ. -/
theorem zero_mem_closed (hR : IsRelativeRootAmbient i R) (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ)
    {X : Set (characterLattice T)} (hX : IsClosedRootSubset R X)
    (hplus : Θ ⊆ X) (hminus : ∀ α ∈ Θ, -α ∈ X)
    {α : characterLattice T} (hα : α ∈ R) (hzero : latticePairing T α ζ = 0) : α ∈ X := by
  have hpos : ∀ β ∈ positiveRootSubset R ν,
      latticePairing T β ζ = 0 → β ∈ X ∧ -β ∈ X := by
    intro β hβ
    apply hR.positive_induction hroot hT hν (hα := hβ)
    · intro γ hγ hzero
      by_cases hγΘ : γ ∈ Θ
      · exact ⟨hplus hγΘ, hminus γ hγΘ⟩
      · have := hζ.2.2 γ hγ hγΘ
        omega
    · intro γ hγ δ hδ hsum hγind hδind hzero
      have hγnonneg := hζ.pairing_nonneg_of_positive i ν ⟨hR.subset_relativeRoots hγ.1, hγ.2⟩
      have hδnonneg := hζ.pairing_nonneg_of_positive i ν ⟨hR.subset_relativeRoots hδ.1, hδ.2⟩
      have hzero' : latticePairing T γ ζ + latticePairing T δ ζ = 0 := by simpa using hzero
      obtain ⟨hγX, hnγX⟩ := hγind (by omega)
      obtain ⟨hδX, hnδX⟩ := hδind (by omega)
      refine ⟨hX.2 γ hγX δ hδX hsum, ?_⟩
      simpa only [neg_add] using hX.2 (-γ) hnγX (-δ) hnδX
        (by simpa only [neg_add] using hR.neg_mem hroot hT hsum)
  rcases lt_or_gt_of_ne (hν α (hR.subset_relativeRoots hα)) with hn | hp
  · have hnegpos : -α ∈ positiveRootSubset R ν :=
      ⟨hR.neg_mem hroot hT hα, by simpa using neg_pos.mpr hn⟩
    have := (hpos (-α) hnegpos (by simp [hzero])).2
    simpa using this
  · exact (hpos α ⟨hα, hp⟩ hzero).1

/-- The integral span of Θ is the zero-pairing locus among actual roots. -/
theorem zero_iff_groupClosure (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    latticePairing T α ζ = 0 ↔ α ∈ AddSubgroup.closure Θ := by
  have hkernel : AddSubgroup.closure Θ ≤
      (((latticePairing T).flip ζ).toAddMonoidHom.ker) := by
    apply (AddSubgroup.closure_le _).mpr
    intro β hβ
    exact hζ.2.1 β hβ
  have hmonoid : AddSubmonoid.closure Θ ≤ (AddSubgroup.closure Θ).toAddSubmonoid :=
    AddSubmonoid.closure_le.mpr (fun _ h => AddSubgroup.subset_closure h)
  refine ⟨fun hzero => ?_, fun h => hkernel h⟩
  rcases lt_or_gt_of_ne (hν α hα) with hn | hp
  · have hnegpos : -α ∈ positiveRelativeRoots i ν :=
      ⟨hroot.neg_mem_relativeRoots i hT hα, by simpa using neg_pos.mpr hn⟩
    have hmem := hmonoid ((hζ.pairing_eq_zero_iff_mem_closure i ν hnegpos).mp
      (by simp [hzero]))
    simpa using (AddSubgroup.closure Θ).neg_mem hmem
  · exact hmonoid ((hζ.pairing_eq_zero_iff_mem_closure i ν ⟨hα, hp⟩).mp hzero)

/-- Positive ζ-pairing forces positivity for the original generic cocharacter. -/
theorem positive_of_pairing_pos (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ)
    {α : characterLattice T} (hα : α ∈ relativeRoots i)
    (hp : 0 < latticePairing T α ζ) : 0 < latticePairing T α ν := by
  rcases lt_or_gt_of_ne (hν α hα) with hn | hpos
  · have := hζ.pairing_nonneg_of_positive i ν
      ⟨hroot.neg_mem_relativeRoots i hT hα, by simpa using neg_pos.mpr hn⟩
    simp only [map_neg, LinearMap.neg_apply] at this
    omega
  · exact hpos

end StandardRootTriple

end Langlands.GroupScheme
