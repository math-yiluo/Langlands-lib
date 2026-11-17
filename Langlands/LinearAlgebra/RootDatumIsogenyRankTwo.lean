import Langlands.LinearAlgebra.RootDatumIsogenyReflections
import Langlands.LinearAlgebra.RootDatumRankTwoBase

/-! # Rank-two scaling patterns of root-datum isogenies -/

noncomputable section

namespace Langlands.LinearAlgebra.RootDatumIsogeny

/-- The possibilities for the two root factors and the corresponding
Cartan entries of two distinct simple roots under a root-datum isogeny.
The orthogonal case allows independent factors. -/
inductive RankTwoScalingPattern (a b a' b' : ℤ) (q r : ℕ) : Type
  | orthogonal (ha : a = 0) (hb : b = 0) (ha' : a' = 0) (hb' : b' = 0)
  | equal (ha : a = a') (hb : b = b') (hqr : q = r)
  | doubleForward (ha : a = -1) (hb : b = -2)
      (ha' : a' = -2) (hb' : b' = -1) (hqr : r = 2 * q)
  | doubleReverse (ha : a = -2) (hb : b = -1)
      (ha' : a' = -1) (hb' : b' = -2) (hqr : q = 2 * r)
  | tripleForward (ha : a = -1) (hb : b = -3)
      (ha' : a' = -3) (hb' : b' = -1) (hqr : r = 3 * q)
  | tripleReverse (ha : a = -3) (hb : b = -1)
      (ha' : a' = -1) (hb' : b' = -3) (hqr : q = 3 * r)

private theorem nonemptyPatternOfCartan
    {a b a' b' : ℤ} {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hab : (a, b) ∈ ({(0, 0), (-1, -1), (-1, -2), (-2, -1),
      (-1, -3), (-3, -1)} : Set (ℤ × ℤ)))
    (hab' : (a', b') ∈ ({(0, 0), (-1, -1), (-1, -2), (-2, -1),
      (-1, -3), (-3, -1)} : Set (ℤ × ℤ)))
    (hscale : (q : ℤ) * a' = (r : ℤ) * a)
    (hscale' : (r : ℤ) * b' = (q : ℤ) * b) :
    Nonempty (RankTwoScalingPattern a b a' b' q r) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hab hab'
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    first
    | exact ⟨.orthogonal rfl rfl rfl rfl⟩
    | exact ⟨.equal rfl rfl (by omega)⟩
    | exact ⟨.doubleForward rfl rfl rfl rfl (by omega)⟩
    | exact ⟨.doubleReverse rfl rfl rfl rfl (by omega)⟩
    | exact ⟨.tripleForward rfl rfl rfl rfl (by omega)⟩
    | exact ⟨.tripleReverse rfl rfl rfl rfl (by omega)⟩
    | exact False.elim (by omega)

section Cartan

variable {J X Y : Type*} [Finite J] [AddCommGroup X] [AddCommGroup Y]
    {P : RootDatum J X Y} [P.IsReduced]

/-- The nonpositive Cartan pairs for distinct roots in a base of a reduced
root datum. -/
theorem cartanPair_mem_of_simple (b : P.Base) {i j : J}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hne : i ≠ j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)} :
        Set (ℤ × ℤ)) := by
  have hli : LinearIndependent ℤ ![P.root i, P.root j] :=
    b.linearIndependent_pair_of_ne (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      (fun h => hne (congrArg Subtype.val h))
  have hroot : P.root i ≠ P.root j := fun h => hne (P.root.injective h)
  have hneg : P.root i ≠ -P.root j := by
    intro h
    have hz : (1 : ℤ) • P.root i + (1 : ℤ) • P.root j = 0 := by simp [h]
    exact (one_ne_zero : (1 : ℤ) ≠ 0) ((LinearIndependent.pair_iff.mp hli) 1 1 hz).1
  have hle := b.pairingIn_le_zero_of_ne hne hi hj
  have hle' := b.pairingIn_le_zero_of_ne hne.symm hj hi
  have h := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j hroot hneg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h1, h2⟩
  all_goals simp_all

end Cartan

variable {p : ℕ} {J X Y J' X' Y' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Finite J] [Finite J']
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X'] [Module.Finite ℤ Y']
    {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
    [P.IsReduced] [Q.IsReduced]

/-- The transpose identity gives the exact weighted Cartan identity. -/
theorem rootFactor_mul_pairingIn (f : RootDatumIsogeny p P Q) (i j : J) :
    (f.rootFactor i : ℤ) * Q.pairingIn ℤ (f.indexEquiv i) (f.indexEquiv j) =
      (f.rootFactor j : ℤ) * P.pairingIn ℤ i j := by
  have h := f.pairing_apply (P.root i) (Q.coroot (f.indexEquiv j))
  rw [f.root_weightMap, f.coroot_coweightMap] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    RootPairing.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ,
    ← Q.algebraMap_pairingIn ℤ] at h
  simpa using h

/-- A prime dividing any root factor must be the characteristic exponent
of the root-datum isogeny. -/
theorem characteristicExponent_eq_of_prime_dvd_rootFactor
    (f : RootDatumIsogeny p P Q) {l : ℕ} (hl : Nat.Prime l)
    (i : J) (hi : l ∣ f.rootFactor i) : p = l := by
  obtain ⟨n, hn⟩ := f.rootFactor_pow i
  rw [hn] at hi
  have hdiv := hl.dvd_of_dvd_pow hi
  rcases f.characteristicExponent with h | hp
  · exact False.elim (hl.not_dvd_one (h ▸ hdiv))
  · exact (((Nat.dvd_prime hp).mp hdiv).resolve_left hl.ne_one).symm

/-- A prime ratio between two root factors forces that characteristic
exponent. In particular the exceptional ratios two and three can occur
only for exponents two and three, respectively. -/
theorem characteristicExponent_eq_of_rootFactor_ratio
    (f : RootDatumIsogeny p P Q) {l : ℕ} (hl : Nat.Prime l)
    (i j : J) (hij : f.rootFactor j = l * f.rootFactor i) : p = l :=
  f.characteristicExponent_eq_of_prime_dvd_rootFactor hl j ⟨f.rootFactor i, hij⟩

/-- Classify the root-factor scaling for two distinct simple roots that
correspond to simple roots in a supplied base of the other datum. -/
def rankTwoScalingPattern (f : RootDatumIsogeny p P Q)
    (b : P.Base) (b' : Q.Base) {i j : J}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hne : i ≠ j)
    (hi' : f.indexEquiv i ∈ b'.support) (hj' : f.indexEquiv j ∈ b'.support) :
    RankTwoScalingPattern
      (P.pairingIn ℤ i j) (P.pairingIn ℤ j i)
      (Q.pairingIn ℤ (f.indexEquiv i) (f.indexEquiv j))
      (Q.pairingIn ℤ (f.indexEquiv j) (f.indexEquiv i))
      (f.rootFactor i) (f.rootFactor j) :=
  Classical.choice <| nonemptyPatternOfCartan (f.rootFactor_pos i) (f.rootFactor_pos j)
    (cartanPair_mem_of_simple b hi hj hne)
    (cartanPair_mem_of_simple b' hi' hj' (fun h => hne (f.indexEquiv.injective h)))
    (f.rootFactor_mul_pairingIn i j) (f.rootFactor_mul_pairingIn j i)

end Langlands.LinearAlgebra.RootDatumIsogeny
