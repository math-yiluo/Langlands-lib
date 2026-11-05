import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Mathlib.Algebra.Module.Rat

/-! # Actual root rays from opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

private theorem eq_of_character_nsmul_eq
    (hS : IsSplitTorus S.toGrp) {r : ℕ} (hr : 0 < r)
    {a b : characterLattice S} (h : r • a = r • b) : a = b := by
  let := IsAddTorsionFree.of_module_rat (ℚ ⊗[ℤ] characterLattice S)
  apply hS.character_toRat_injective
  apply nsmul_right_injective (Nat.ne_of_gt hr)
  simpa only [← map_nsmul] using congrArg toRat h

variable [Smooth G.X.hom]

private theorem HasOppositeFactorPairs.exists_rootCoroot
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (a : relativeRoots i) :
    ∃ c : cocharacterLattice S, latticePairing S a.val c = 2 := by
  obtain ⟨x, hx, hx1⟩ := exists_rootPoint_actual hS i a.property
  obtain ⟨p, hp⟩ := hE a.val a.property x hx hx1
  exact ⟨hp.coroot i hS a.property.1 hx hx1,
    (hp.coroot_spec i hS a.property.1 hx hx1).1⟩

/-- Choose an actual integral cocharacter pairing to two with each actual root.
Its existence uses a nonidentity root point and an opposite factor pair. -/
def HasOppositeFactorPairs.rootCoroot
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (a : relativeRoots i) : cocharacterLattice S :=
  Classical.choose (hE.exists_rootCoroot i hS a)

/-- The chosen integral cocharacter has the required self-pairing. -/
theorem HasOppositeFactorPairs.rootCoroot_pairing
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (a : relativeRoots i) :
    latticePairing S a.val (hE.rootCoroot i hS a) = 2 :=
  Classical.choose_spec (hE.exists_rootCoroot i hS a)

/-- Opposite-pair existence classifies actual roots with a common positive
integral multiple, without a relative-root-system premise. -/
theorem HasOppositeFactorPairs.root_eq_or_twice_of_common_positive_multiple
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    {a b : characterLattice S} (ha : a ∈ relativeRoots i)
    (hb : b ∈ relativeRoots i) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m • a = n • b) :
    a = b ∨ a = 2 • b ∨ b = 2 • a := by
  let ca := hE.rootCoroot i hS ⟨a, ha⟩
  let cb := hE.rootCoroot i hS ⟨b, hb⟩
  have hselfa : latticePairing S a ca = 2 := hE.rootCoroot_pairing i hS ⟨a, ha⟩
  have hselfb : latticePairing S b cb = 2 := hE.rootCoroot_pairing i hS ⟨b, hb⟩
  have hca : 2 * (m : ℤ) = (n : ℤ) * latticePairing S b ca := by
    have hp := congrArg (fun χ => latticePairing S χ ca) h
    simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      hselfa, mul_comm] using hp
  have hcb : (m : ℤ) * latticePairing S a cb = 2 * (n : ℤ) := by
    have hp := congrArg (fun χ => latticePairing S χ cb) h
    simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      hselfb, mul_comm] using hp
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  have hnz : 0 < (n : ℤ) := by exact_mod_cast hn
  have hprod : latticePairing S b ca * latticePairing S a cb = 4 := by
    apply mul_left_cancel₀ (ne_of_gt hnz)
    calc
      (n : ℤ) * (latticePairing S b ca * latticePairing S a cb) =
          ((n : ℤ) * latticePairing S b ca) * latticePairing S a cb := by ring
      _ = (2 * (m : ℤ)) * latticePairing S a cb := by rw [← hca]
      _ = 2 * ((m : ℤ) * latticePairing S a cb) := by ring
      _ = (n : ℤ) * 4 := by rw [hcb]; ring
  have hpos : 0 < latticePairing S b ca := by nlinarith
  have hpos' : 0 < latticePairing S a cb := by nlinarith
  have hle : latticePairing S b ca ≤ 4 := by nlinarith
  interval_cases hp : latticePairing S b ca
  · have hn' : n = m * 2 := by omega
    right
    left
    apply eq_of_character_nsmul_eq hS hm
    calc
      m • a = n • b := h
      _ = (m * 2) • b := by rw [hn']
      _ = m • (2 • b) := by rw [smul_smul]
  · have hmn : m = n := by omega
    left
    subst n
    exact eq_of_character_nsmul_eq hS hm h
  · omega
  · have hm' : m = n * 2 := by omega
    right
    right
    apply eq_of_character_nsmul_eq hS hn
    calc
      n • b = m • a := h.symm
      _ = (n * 2) • a := by rw [hm']
      _ = n • (2 • a) := by rw [smul_smul]

/-- Distinct actual indivisible roots have disjoint positive integral rays
when every nonidentity actual root point admits an opposite factor pair. -/
theorem HasOppositeFactorPairs.disjoint_cyclicTail_indivisibleRoots
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    {a b : characterLattice S} (ha : a ∈ indivisibleRoots i)
    (hb : b ∈ indivisibleRoots i) (hne : a ≠ b) :
    Disjoint (cyclicTail a 1 : Set (characterLattice S))
      (cyclicTail b 1 : Set (characterLattice S)) := by
  apply Set.disjoint_left.mpr
  rintro χ ⟨m, _, hm, hma⟩ ⟨n, _, hn, hnb⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hS
      ha.1 hb.1 hm hn (hma.trans hnb.symm) with heq | heq | heq
  · exact hne heq
  · exact ha.2 b hb.1 2 (by omega) heq.symm
  · exact hb.2 a ha.1 2 (by omega) heq.symm

/-- The exact global ray proposition follows from the existing rank-one
factorization proposition, retaining every field and cocharacter. -/
theorem relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement
    (hRankOne : RootRankOneFactorizationStatement.{u}) :
    RelativeRootRayDecompositionStatement.{u} := by
  intro k _ G hG S i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro ν
  have hE : HasOppositeFactorPairs i :=
    (hasRankOneFactorization_iff_hasOppositeFactorPairs i hi.isSplitSubtorus.1).mp
      (hRankOne k G hG S i hi)
  obtain ⟨n, a, hinj, hrange⟩ := indivisiblePositiveRootEnumeration i ν
    (hi.isSplitSubtorus.1.finite_relativeRoots i)
  refine ⟨⟨n, a, hinj, hrange⟩, ?_, ?_⟩
  · intro a ha b hb hne
    exact hE.disjoint_cyclicTail_indivisibleRoots i hi.isSplitSubtorus.1
      ha.1 hb.1 hne
  · intro χ hχ
    exact positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ

end Langlands.GroupScheme.RelativeRoot
