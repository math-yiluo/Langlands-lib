import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

/-! # Positive integral rays of actual relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace RootPairing

/-- Two roots with a common positive integral multiple agree up to doubling.
No reducedness assumption is used. -/
theorem root_eq_or_twice_of_common_positive_multiple
    {J M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [Finite J]
    (P : RootPairing J ℚ M N) [P.IsCrystallographic]
    (r s : J) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root r = n • P.root s) :
    P.root r = P.root s ∨
      P.root r = 2 • P.root s ∨ P.root s = 2 • P.root r := by
  have hdep : ¬ LinearIndependent ℚ ![P.root r, P.root s] := by
    rw [LinearIndependent.pair_iff]
    push Not
    refine ⟨(m : ℚ), -(n : ℚ), ?_, ?_⟩
    · simpa only [neg_smul, add_neg_eq_zero, Nat.cast_smul_eq_nsmul] using h
    · simp [Nat.ne_of_gt hm]
  have hprod : P.pairingIn ℤ r s * P.pairingIn ℤ s r = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
  have hpair : (m : ℤ) * P.pairingIn ℤ r s = 2 * (n : ℤ) := by
    have heq := congrArg (P.coroot' s) h
    have heq' : (m : ℚ) * (P.pairingIn ℤ r s : ℚ) = 2 * (n : ℚ) := by
      simpa [P.coroot_root_eq_pairing, ← P.algebraMap_pairingIn ℤ,
        mul_comm] using heq
    exact_mod_cast heq'
  have hpos : 0 < P.pairingIn ℤ r s := by
    have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
    have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
    nlinarith
  have hpos' : 0 < P.pairingIn ℤ s r := by nlinarith
  have hle : P.pairingIn ℤ r s ≤ 4 := by nlinarith
  interval_cases hp : P.pairingIn ℤ r s
  · have hq : P.pairingIn ℤ s r = 4 := by omega
    right
    right
    simpa only [two_smul] using
      (P.pairingIn_one_four_iff ℤ r s).mp ⟨hp, hq⟩
  · have hq : P.pairingIn ℤ s r = 2 := by omega
    left
    exact congrArg P.root ((P.pairingIn_two_two_iff ℤ r s).mp ⟨hp, hq⟩)
  · omega
  · have hq : P.pairingIn ℤ s r = 1 := by omega
    right
    left
    simpa only [two_smul] using
      (P.pairingIn_one_four_iff ℤ s r).mp ⟨hq, hp⟩

end RootPairing

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Integral positivity gives descent to an actual indivisible root.
Finiteness and a root-system realization are unnecessary for this implication. -/
theorem exists_indivisiblePositiveRoot_ray
    {χ : characterLattice S} (hχ : χ ∈ relativeRoots i)
    (hpos : 0 < latticePairing S χ ν) :
    ∃ a ∈ indivisiblePositiveRoots i ν, χ ∈ cyclicTail a 1 := by
  suffices ∀ d : ℕ, ∀ χ ∈ relativeRoots i, 0 < latticePairing S χ ν →
      (latticePairing S χ ν).toNat = d →
      ∃ a ∈ indivisiblePositiveRoots i ν, χ ∈ cyclicTail a 1 from
    this _ χ hχ hpos rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro χ hχ hpos hd
    by_cases hmin : χ ∈ indivisibleRoots i
    · exact ⟨χ, ⟨hmin, hpos⟩, 1, by omega, by omega, by simp⟩
    · obtain ⟨b, hb, m, hm, hmb⟩ :
          ∃ b ∈ relativeRoots i, ∃ m : ℕ, 1 < m ∧ m • b = χ := by
        simpa only [indivisibleRoots, Set.mem_ofPred_eq, hχ, true_and,
          not_forall, not_not, exists_prop] using hmin
      have hmul : (m : ℤ) * latticePairing S b ν = latticePairing S χ ν := by
        rw [← hmb]
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : 1 < (m : ℤ) := by exact_mod_cast hm
      have hbpos : 0 < latticePairing S b ν := by nlinarith
      have hless : (latticePairing S b ν).toNat < d := by
        have : latticePairing S b ν < latticePairing S χ ν := by nlinarith
        omega
      obtain ⟨a, ha, n, hn, hn0, hna⟩ := ih _ hless b hb hbpos rfl
      have hmn := Nat.mul_pos (show 0 < m by omega) hn0
      refine ⟨a, ha, m * n, by omega, hmn, ?_⟩
      rw [← smul_smul, hna, hmb]

/-- For an actual root, positivity is exactly membership in an indivisible
positive root ray; points of a ray need not themselves be roots. -/
theorem positive_iff_mem_indivisiblePositiveRoot_ray
    {χ : characterLattice S} (hχ : χ ∈ relativeRoots i) :
    0 < latticePairing S χ ν ↔
      ∃ a ∈ indivisiblePositiveRoots i ν, χ ∈ cyclicTail a 1 := by
  refine ⟨exists_indivisiblePositiveRoot_ray i ν hχ, ?_⟩
  rintro ⟨a, ha, m, _, hm, rfl⟩
  have hpos := ha.2
  have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
  simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using
    mul_pos hm' hpos

/-- Any finite actual root set has a finite injective enumeration of the
indivisible positive roots selected by any cocharacter. -/
theorem exists_fin_enumeration_indivisiblePositiveRoots
    (hfin : (relativeRoots i).Finite) :
    ∃ (n : ℕ) (a : Fin n → characterLattice S),
      Function.Injective a ∧ Set.range a = indivisiblePositiveRoots i ν :=
  (hfin.subset fun _ ha => ha.1.1).fin_param

/-- A chosen finite enumeration, together with its injectivity and exact range.
The enumeration carries no ordering or canonicity assertion. -/
def indivisiblePositiveRootEnumeration
    (hfin : (relativeRoots i).Finite) :
    Σ n : ℕ, {a : Fin n → characterLattice S //
      Function.Injective a ∧ Set.range a = indivisiblePositiveRoots i ν} := by
  let hex := exists_fin_enumeration_indivisiblePositiveRoots i ν hfin
  exact ⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex),
    Classical.choose_spec (Classical.choose_spec hex)⟩

variable [Mono i.hom.hom.left]

/-- Distinct roots indivisible within the actual root set have disjoint
positive integral rays, under the actual relative-root-system realization. -/
theorem disjoint_cyclicTail_indivisibleRoots
    (hroot : HasRelativeRootSystem i) (hS : IsSplitTorus S.toGrp)
    {a b : characterLattice S} (ha : a ∈ indivisibleRoots i)
    (hb : b ∈ indivisibleRoots i) (hne : a ≠ b) :
    Disjoint (cyclicTail a 1 : Set (characterLattice S))
      (cyclicTail b 1 : Set (characterLattice S)) := by
  obtain ⟨J, hJ, P, _, hcrys, _, hroots, _, _⟩ := hroot
  have := hJ
  have := hcrys
  have hrep (c : characterLattice S) (hc : c ∈ relativeRoots i) :
      ∃ r : J, (P.root r : ℚ ⊗[ℤ] characterLattice S) = toRat c := by
    have hx : toRat c ∈ Subtype.val '' Set.range P.root := by
      rw [hroots]
      exact Set.mem_image_of_mem _ hc
    obtain ⟨_, ⟨r, rfl⟩, hr⟩ := hx
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hrep a ha.1
  obtain ⟨s, hs⟩ := hrep b hb.1
  apply Set.disjoint_left.mpr
  rintro χ ⟨m, _, hm, hma⟩ ⟨n, _, hn, hnb⟩
  have hmult : m • P.root r = n • P.root s := by
    apply Subtype.ext
    change m • (P.root r : ℚ ⊗[ℤ] characterLattice S) =
      n • (P.root s : ℚ ⊗[ℤ] characterLattice S)
    rw [hr, hs, ← map_nsmul, ← map_nsmul, hma, hnb]
  rcases P.root_eq_or_twice_of_common_positive_multiple r s hm hn hmult with
    heq | heq | heq
  · apply hne
    apply hS.character_toRat_injective
    rw [← hr, ← hs]
    exact congrArg Subtype.val heq
  · apply ha.2 b hb.1 2 (by omega)
    apply hS.character_toRat_injective
    rw [map_nsmul, ← hs, ← hr]
    exact (congrArg Subtype.val heq).symm
  · apply hb.2 a ha.1 2 (by omega)
    apply hS.character_toRat_injective
    rw [map_nsmul, ← hr, ← hs]
    exact (congrArg Subtype.val heq).symm

/-- Reduction of the complete ray target to the existing general relative-root
system target, retaining every universe, field and cocharacter hypothesis. -/
theorem relativeRootRayDecompositionStatement_of_relativeRootSystemStatement
    (hroot : RelativeRootSystemStatement.{u}) :
    RelativeRootRayDecompositionStatement.{u} := by
  intro k _ G hG S i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν
  have hroots : HasRelativeRootSystem i := hroot k G hG S i hi
  obtain ⟨n, a, hinj, hrange⟩ := indivisiblePositiveRootEnumeration i ν
    (hroots.finite_relativeRoots i hi.isSplitSubtorus.1)
  refine ⟨⟨n, a, hinj, hrange⟩, ?_, ?_⟩
  · intro a ha b hb hne
    exact disjoint_cyclicTail_indivisibleRoots i hroots hi.isSplitSubtorus.1
      ha.1 hb.1 hne
  · intro χ hχ
    exact positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ

end Langlands.GroupScheme.RelativeRoot
