import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Rational.RootCommutingPartition
import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation
import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! # Reflection-invariant subspaces give commuting root partitions -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace RootPairing

variable {J V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : RootPairing J ℚ V W)

/-- Roots on opposite sides of an invariant subspace have no strict positive
mixed root combination. No crystallographic or reducedness assumption is used. -/
theorem invtRootSubmodule.no_strict_mixed_roots
    (q : P.invtRootSubmodule) {a b : J}
    (ha : P.root a ∈ (q : Submodule ℚ V))
    (hb : P.root b ∉ (q : Submodule ℚ V))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • P.root a + m • P.root b ≠ 0 ∧
      n • P.root a + m • P.root b ∉ Set.range P.root := by
  have hab : P.coroot' b (P.root a) = 0 :=
    LinearMap.mem_ker.mp (RootPairing.invtRootSubmodule.le_ker_coroot' q hb ha)
  have hba : P.coroot' a (P.root b) = 0 := by
    rw [P.root_coroot'_eq_pairing, ← P.pairing_eq_zero_iff']
    rwa [P.root_coroot'_eq_pairing] at hab
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hbmix : P.coroot' b (n • P.root a + m • P.root b) = (m : ℚ) * 2 := by
    simp [map_add, map_nsmul, hab, P.root_coroot'_eq_pairing,
      nsmul_eq_mul]
  constructor
  · intro hz
    have h := hbmix
    rw [hz, map_zero] at h
    exact (mul_ne_zero hm0 (by norm_num)) h.symm
  · rintro ⟨c, hc⟩
    by_cases hcmem : P.root c ∈ (q : Submodule ℚ V)
    · have h := LinearMap.mem_ker.mp (RootPairing.invtRootSubmodule.le_ker_coroot' q hb hcmem)
      rw [hc, hbmix] at h
      exact (mul_ne_zero hm0 (by norm_num)) h
    · have hac : P.coroot' c (P.root a) = 0 :=
        LinearMap.mem_ker.mp (RootPairing.invtRootSubmodule.le_ker_coroot' q hcmem ha)
      have hca : P.coroot' a (P.root c) = 0 := by
        rw [P.root_coroot'_eq_pairing, ← P.pairing_eq_zero_iff']
        rwa [P.root_coroot'_eq_pairing] at hac
      rw [hc] at hca
      have he : P.coroot' a (n • P.root a + m • P.root b) = (n : ℚ) * 2 := by
        simp [map_add, map_nsmul, hba, P.root_coroot'_eq_pairing,
          nsmul_eq_mul]
      rw [he] at hca
      exact (mul_ne_zero hn0 (by norm_num)) hca

end RootPairing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G)

/-- The actual roots whose rational images belong to the specified subspace
of the actual rational root span. -/
def rationalRootPart (q : Submodule ℚ (relativeRootSpan i)) : Set (characterLattice S) :=
  {a | ∃ ha : a ∈ relativeRoots i,
    (⟨toRat a, toRat_mem_ratSpan ha⟩ : relativeRootSpan i) ∈ q}

theorem rationalRootPart_subset (q : Submodule ℚ (relativeRootSpan i)) :
    rationalRootPart i q ⊆ relativeRoots i :=
  fun _ ha => ha.choose

section FullRootImage

variable {J W : Type*} [AddCommGroup W] [Module ℚ W]
  (P : RootPairing J ℚ (relativeRootSpan i) W)
  (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)

include hP

/-- A full actual-root image supplies an index for every actual root. -/
theorem exists_root_eq_rationalRoot {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ∃ j, P.root j = ⟨toRat a, toRat_mem_ratSpan ha⟩ := by
  have hav : toRat a ∈ Subtype.val '' Set.range P.root := by
    rw [hP]
    exact ⟨a, ha, rfl⟩
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hav
  exact ⟨j, Subtype.ext hj⟩

end FullRootImage

section InvariantPartition

variable {J W : Type*} [AddCommGroup W] [Module ℚ W]
  (P : RootPairing J ℚ (relativeRootSpan i) W)
  (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)

include hP

/-- Reflection invariance gives commutation across the corresponding actual
root partition, on arbitrary scheme tests. -/
theorem isCommutingRootPartition_rationalRootPart
    [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp) (q : P.invtRootSubmodule) :
    IsCommutingRootPartition i (rationalRootPart i q) := by
  intro a ha b hb hbs Z x y hx hy
  obtain ⟨ha, hqa⟩ := ha
  obtain ⟨ja, hja⟩ := exists_root_eq_rationalRoot i P hP ha
  obtain ⟨jb, hjb⟩ := exists_root_eq_rationalRoot i P hP hb
  have hqa' : P.root ja ∈ (q : Submodule ℚ (relativeRootSpan i)) := by
    rwa [hja]
  have hqb' : P.root jb ∉ (q : Submodule ℚ (relativeRootSpan i)) := by
    intro h
    apply hbs
    exact ⟨hb, by rwa [hjb] at h⟩
  apply RootPairNoncommutation.commute_of_no_strict_combinations hS i a b ha.1 hb.1
    (fun n m hn hm => ?_) hx hy
  have hmix := RootPairing.invtRootSubmodule.no_strict_mixed_roots P q hqa' hqb' n m hn hm
  constructor
  · intro hz
    apply hmix.1
    apply Subtype.ext
    change n • (P.root ja).val + m • (P.root jb).val = 0
    rw [hja, hjb]
    simpa only [map_add, map_nsmul, map_zero] using congrArg toRat hz
  · intro hroot
    obtain ⟨jc, hjc⟩ := exists_root_eq_rationalRoot i P hP hroot
    apply hmix.2
    refine ⟨jc, Subtype.ext ?_⟩
    change (P.root jc).val = n • (P.root ja).val + m • (P.root jb).val
    rw [hjc, hja, hjb]
    simp only [map_add, map_nsmul]

/-- In an almost-simple group a nonzero reflection-invariant subspace of a
full actual-root system is the whole rational root span. -/
theorem invtRootSubmodule_eq_top_of_ne_bot
    [P.IsRootSystem] (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    (q : P.invtRootSubmodule) (hq : q ≠ ⊥) : q = ⊤ := by
  classical
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  have hcomm := isCommutingRootPartition_rationalRootPart i P hP hi.1.1 q
  rcases hcomm.eq_empty_or_eq_relativeRoots i hG hi (rationalRootPart_subset i q) with
    hempty | hfull
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j, P.root j ∈ (q : Submodule ℚ (relativeRootSpan i)) := by
      by_contra h
      exact hq ((RootPairing.invtRootSubmodule.eq_bot_iff q).mpr
        (by simpa only [not_exists] using h))
    have himage : (P.root j).val ∈ toRat '' relativeRoots i := by
      rw [← hP]
      exact ⟨P.root j, ⟨j, rfl⟩, rfl⟩
    obtain ⟨a, ha, hja⟩ := himage
    have hja' : P.root j = ⟨toRat a, toRat_mem_ratSpan ha⟩ := Subtype.ext hja.symm
    have hmem : a ∈ rationalRootPart i q := ⟨ha, by rwa [← hja']⟩
    rw [hempty] at hmem
    exact hmem
  · apply (RootPairing.invtRootSubmodule.eq_top_iff q).mpr
    rintro _ ⟨j, rfl⟩
    have himage : (P.root j).val ∈ toRat '' relativeRoots i := by
      rw [← hP]
      exact ⟨P.root j, ⟨j, rfl⟩, rfl⟩
    obtain ⟨a, ha, hja⟩ := himage
    have hmem : a ∈ rationalRootPart i q := hfull.symm ▸ ha
    obtain ⟨ha, hqa⟩ := hmem
    have hj : P.root j = ⟨toRat a, toRat_mem_ratSpan ha⟩ := Subtype.ext hja.symm
    rwa [hj]

/-- Any root system with the full actual-root image of a maximal split torus
in an almost-simple group is irreducible when that root set is nonempty. -/
theorem isIrreducible_of_full_relativeRoot_image
    [P.IsRootSystem] (hG : IsAlmostSimple G) (hi : IsMaximalSplitTorus i)
    (hne : (relativeRoots i).Nonempty) : P.IsIrreducible := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨j, _⟩ := exists_root_eq_rationalRoot i P hP ha
  let : Nontrivial (relativeRootSpan i) := ⟨⟨P.root j, 0, P.ne_zero j⟩⟩
  apply RootPairing.IsIrreducible.mk' P
  intro q hq hqbot
  let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
  have hq' : q' ≠ ⊥ := by
    intro h
    exact hqbot (congrArg Subtype.val h)
  exact congrArg Subtype.val (invtRootSubmodule_eq_top_of_ne_bot i P hP hG hi q' hq')

end InvariantPartition

end Langlands.GroupScheme
