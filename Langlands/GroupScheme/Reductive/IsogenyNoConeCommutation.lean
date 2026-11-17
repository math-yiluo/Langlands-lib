import Langlands.GroupScheme.Reductive.B2PowerCommutatorTransport
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity
import Langlands.GroupScheme.Reductive.NormalizedLocalRootFamily
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormal
import Langlands.LinearAlgebra.RootDatumIsogenyBases
import Langlands.LinearAlgebra.RootDatumIsogenyRankTwo

/-! # No-cone commutation under a root-datum isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IsogenyNoCone

open LocalSplitCell

variable {I I' J J' : Type u} [Fintype I] [Fintype I']
    [Finite J] [Finite J']
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    [P.IsReduced] [Q.IsReduced] {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

/-- No root is a positive integral mixed combination of the two given roots. -/
def NoMixedRoot (P : RootDatum J (I → ℤ) (I → ℤ)) (x y : J) : Prop :=
  ∀ (z : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
    (s : ℤ) • P.root x + (t : ℤ) • P.root y ≠ P.root z

omit [Fintype I] [Finite J] [P.IsReduced] in
theorem NoMixedRoot.symm {x y : J} (h : NoMixedRoot P x y) : NoMixedRoot P y x :=
  fun z s t hs ht => by simpa only [add_comm] using h z t s ht hs

theorem indexEquiv_word (l : List J') (x : J') :
    f.indexEquiv (Langlands.LinearAlgebra.wordPerm Q l x) =
      Langlands.LinearAlgebra.wordPerm P (l.map f.indexEquiv) (f.indexEquiv x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [wordPerm_cons, List.map_cons,
      f.indexEquiv_reflectionPerm, ih]

theorem target_not_opposite {x y : J'}
    (h : P.root (f.indexEquiv x) ≠ -P.root (f.indexEquiv y)) :
    Q.root x ≠ -Q.root y := by
  intro he
  have hi : x = Q.reflectionPerm y y := Q.root.injective (by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] using he)
  apply h
  rw [hi, f.indexEquiv_reflectionPerm, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

omit [Fintype I] [P.IsReduced] in
theorem pairing_nonneg_of_noMixedRoot {x y : J}
    (hneg : P.root x ≠ -P.root y) (hcone : NoMixedRoot P x y) :
    0 ≤ P.pairingIn ℤ x y := by
  by_contra hn
  obtain ⟨z, hz⟩ := P.root_add_root_mem_of_pairingIn_neg (lt_of_not_ge hn) hneg
  exact hcone z 1 1 le_rfl le_rfl (by simpa only [Nat.cast_one, one_smul] using hz.symm)

theorem target_pairing_nonneg {x y : J'}
    (hneg : P.root (f.indexEquiv x) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv x) (f.indexEquiv y)) :
    0 ≤ Q.pairingIn ℤ x y := by
  have hp := pairing_nonneg_of_noMixedRoot hneg hcone
  have hs := f.rootFactor_mul_pairingIn x y
  have hqx : 0 < (f.rootFactor x : ℤ) := by exact_mod_cast f.rootFactor_pos x
  have hqy : 0 < (f.rootFactor y : ℤ) := by exact_mod_cast f.rootFactor_pos y
  nlinarith

omit [Fintype I] [Finite J] [P.IsReduced] in
theorem noMixedRoot_of_word {x y x' y' : J} (l : List J)
    (hx : Langlands.LinearAlgebra.wordPerm P l x' = x)
    (hy : Langlands.LinearAlgebra.wordPerm P l y' = y)
    (h : NoMixedRoot P x y) : NoMixedRoot P x' y' := by
  intro z s t hs ht he
  apply h (Langlands.LinearAlgebra.wordPerm P l z) s t hs ht
  have hw := congrArg (wordReflect P l) he
  rw [Langlands.LinearAlgebra.wordReflect_combo,
    ← Langlands.LinearAlgebra.root_wordPerm, ← Langlands.LinearAlgebra.root_wordPerm,
    ← Langlands.LinearAlgebra.root_wordPerm, hx, hy] at hw
  exact hw

omit [Fintype I] [Finite J] [P.IsReduced] in
theorem not_opposite_of_word {x y x' y' : J} (l : List J)
    (hx : Langlands.LinearAlgebra.wordPerm P l x' = x)
    (hy : Langlands.LinearAlgebra.wordPerm P l y' = y)
    (h : P.root x ≠ -P.root y) : P.root x' ≠ -P.root y' := by
  intro he
  apply h
  have hw := congrArg (wordReflect P l) he
  rw [← Langlands.LinearAlgebra.root_wordPerm, wordReflect_neg,
    ← Langlands.LinearAlgebra.root_wordPerm, hx, hy] at hw
  exact hw

section Points

variable {R : Type u} [CommRing R] {H : GroupScheme (Spec (CommRingCat.of R))}

theorem pointsCommute_self (w : Ga R ⟶ H) : PointsCommute w w := by
  intro B _ s x y
  rw [← rootPoint_add, ← rootPoint_add, add_comm]

omit [Fintype I] in
theorem pointsCommute_wordConj {K : Type u}
    {D : RootDatum K (I → ℤ) (I → ℤ)}
    (u : K → (Ga R ⟶ H)) (l : List K) {w w' : Ga R ⟶ H}
    (h : PointsCommute w w') :
    PointsCommute (wordConj D u l w) (wordConj D u l w') := by
  intro B _ s x y
  rw [rootPoint_wordConj, rootPoint_wordConj]
  let g := wordPoint (P := D) u l (Over.mk s)
  calc
    (g * rootPoint w _ x * g⁻¹) * (g * rootPoint w' _ y * g⁻¹) =
        g * (rootPoint w _ x * rootPoint w' _ y) * g⁻¹ := by group
    _ = g * (rootPoint w' _ y * rootPoint w _ x) * g⁻¹ := by rw [h B s x y]
    _ = (g * rootPoint w' _ y * g⁻¹) * (g * rootPoint w _ x * g⁻¹) := by group

variable [IsLocalRing R] [IsAffineHom H.X.hom] [DecidableEq I']
    {i : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    (hQ : IsFibrewiseRootDatumOf I' H i Q)

include hQ in
omit [Finite J'] [Q.IsReduced] [DecidableEq I'] in
theorem pointsCommute_of_rootParametrizations {x y : J'} {w w' v v' : Ga R ⟶ H}
    (h : PointsCommute w w')
    (hw : IsRootParametrization i (Q.root x) w)
    (hw' : IsRootParametrization i (Q.root y) w')
    (hv : IsRootParametrization i (Q.root x) v)
    (hv' : IsRootParametrization i (Q.root y) v') :
    PointsCommute v v' := by
  obtain ⟨c, hc, -⟩ := hv.existsUnique_unit_of_rootDatum hQ x hw
  obtain ⟨c', hc', -⟩ := hv'.existsUnique_unit_of_rootDatum hQ y hw'
  exact h.of_scaleHom c c' hc hc'

end Points

section ExceptionalCharacteristic

variable {R : Type u} [CommRing R]
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    {b : P.Base} {b' : Q.Base}
    (hb : ∀ j' ∈ b'.support, f.indexEquiv j' ∈ b.support)

include hchar in
theorem ringChar_of_factor_ratio {l : ℕ} (hl : l.Prime) (a c : J')
    (hr : f.rootFactor c = l * f.rootFactor a) : (l : R) = 0 := by
  have hp := f.characteristicExponent_eq_of_rootFactor_ratio hl a c hr
  have hc : f.rootFactor c ≠ 1 := by
    have ha := f.rootFactor_pos a
    have hl2 := hl.two_le
    nlinarith
  simpa only [hp] using hchar c hc

include hb hchar in
theorem char_two_of_b2_noMixedRoot {a c : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -2)
    (hcone : NoMixedRoot P (f.indexEquiv a)
      (f.indexEquiv (Q.reflectionPerm c a))) : (2 : R) = 0 := by
  cases f.rankTwoScalingPattern b' b ha hc hac (hb a ha) (hb c hc) with
  | orthogonal h _ _ _ => omega
  | equal he1 he2 _ =>
    have hp1 : P.pairingIn ℤ (f.indexEquiv a) (f.indexEquiv c) = -1 := he1.symm.trans h1
    have hp2 : P.pairingIn ℤ (f.indexEquiv c) (f.indexEquiv a) = -2 := he2.symm.trans h2
    obtain ⟨r1, r2⟩ := b2_roots hp1 hp2
    apply False.elim
    apply hcone (P.reflectionPerm (f.indexEquiv a) (f.indexEquiv c)) 1 1 le_rfl le_rfl
    simp only [Nat.cast_one, one_smul, f.indexEquiv_reflectionPerm]
    rw [r1, r2]
    module
  | doubleForward _ _ _ _ hr =>
    exact ringChar_of_factor_ratio f hchar Nat.prime_two a c hr
  | doubleReverse h _ _ _ _ => omega
  | tripleForward _ h _ _ _ => omega
  | tripleReverse h _ _ _ _ => omega

include hb hchar in
theorem char_three_of_g2_noMixedRoot {a c : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -3)
    (hcone : NoMixedRoot P (f.indexEquiv a)
      (f.indexEquiv (Q.reflectionPerm a (Q.reflectionPerm c a)))) : (3 : R) = 0 := by
  cases f.rankTwoScalingPattern b' b ha hc hac (hb a ha) (hb c hc) with
  | orthogonal h _ _ _ => omega
  | equal he1 he2 _ =>
    have hp1 : P.pairingIn ℤ (f.indexEquiv a) (f.indexEquiv c) = -1 := he1.symm.trans h1
    have hp2 : P.pairingIn ℤ (f.indexEquiv c) (f.indexEquiv a) = -3 := he2.symm.trans h2
    obtain ⟨r1, r2, r3, -⟩ := g2_roots hp1 hp2
    apply False.elim
    apply hcone (P.reflectionPerm (f.indexEquiv a) (f.indexEquiv c)) 1 1 le_rfl le_rfl
    simp only [Nat.cast_one, one_smul, f.indexEquiv_reflectionPerm]
    rw [r2, r3]
    module
  | doubleForward _ h _ _ _ => omega
  | doubleReverse h _ _ _ _ => omega
  | tripleForward _ _ _ _ hr =>
    exact ringChar_of_factor_ratio f hchar Nat.prime_three a c hr
  | tripleReverse h _ _ _ _ => omega

end ExceptionalCharacteristic

section StandardPairs

variable {R : Type u} [CommRing R] [IsLocalRing R] [DecidableEq I']
    {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    {b : P.Base} {b' : Q.Base}
    {W : ∀ α, SimpleWord Q b' α} {u : J' → (Ga R ⟶ H)}
    (hd : IsNormalSimpleData i Q b' W u)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (hb : ∀ j' ∈ b'.support, f.indexEquiv j' ∈ b.support)

include hd in
omit [Finite J'] [Q.IsReduced] in
theorem pointsCommute_of_word {a d y : J'} {l : List J'}
    (hl : ∀ c ∈ l, c ∈ b'.support)
    (hy : Langlands.LinearAlgebra.wordPerm Q l d = y)
    (h : PointsCommute (weylFamily Q W u a)
      (wordConj Q u l (weylFamily Q W u d))) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  have hp : IsRootParametrization i (Q.root y)
      (wordConj Q u l (weylFamily Q W u d)) := by
    have hp := isRootParametrization_wordConj l
      (fun c hc => hd.weyl c (hl c hc)) (hd.isRootParametrization d)
    rw [← Langlands.LinearAlgebra.root_wordPerm, hy] at hp
    exact hp
  exact pointsCommute_of_rootParametrizations hd.rootDatum h
    (hd.isRootParametrization a) hp
    (hd.isRootParametrization a) (hd.isRootParametrization y)

omit [DecidableEq I'] in
theorem nonneg_pairing_combo {a c y : J'} {m n : ℤ}
    (hneg : P.root (f.indexEquiv a) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv a) (f.indexEquiv y))
    (hy : Q.root y = m • Q.root a + n • Q.root c) :
    0 ≤ m * 2 + n * Q.pairing c a := by
  have hn : P.root (f.indexEquiv y) ≠ -P.root (f.indexEquiv a) := by
    intro h
    apply hneg
    rw [h, neg_neg]
  have hp := target_pairing_nonneg f hn hcone.symm
  have hp' : 0 ≤ Q.pairing y a := by
    rw [← Q.algebraMap_pairingIn ℤ]
    simpa using hp
  rw [pairing_combo hy a, RootPairing.pairing_same] at hp'
  exact hp'

include hd in
omit [IsLocalRing R] in
theorem commute_a1a1 {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h2 : Q.pairingIn ℤ c a = 0) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hya : y ≠ a) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.a1a1_coeffs ha hc hac h2
    (α := z) (p := v) (q := w) hz
  rcases Langlands.LinearAlgebra.a1a1_coeffs_of_nonneg ha hc hac h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hy
  · exact False.elim (hya (Q.root.injective (by simpa using hy)))
  · have ra : Q.root a = (1 : ℤ) • Q.root a + (0 : ℤ) • Q.root c := by simp
    have hn := noOpp_cone_of_coeffs hli ra hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn.1 hn.2

include hd in
omit [IsLocalRing R] in
theorem commute_a2 {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -1) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hya : y ≠ a)
    (hneg : P.root (f.indexEquiv a) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv a) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.a2_coeffs ha hc hac h1 h2
    (α := z) (p := v) (q := w) hz
  have hn := nonneg_pairing_combo f hneg hcone hy
  rw [pairing_eq_of_pairingIn h2] at hn
  rcases Langlands.LinearAlgebra.a2_coeffs_of_nonneg ha hc hac h1 h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hy hn
  · exact False.elim (hya (Q.root.injective (by simpa using hy)))
  · norm_num at hn
  · have ra : Q.root a = (1 : ℤ) • Q.root a + (0 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli ra hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2

include hd hchar hb in
theorem commute_b2_short {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -2) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hya : y ≠ a)
    (hneg : P.root (f.indexEquiv a) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv a) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2
    (α := z) (p := v) (q := w) hz
  have hn := nonneg_pairing_combo f hneg hcone hy
  rw [pairing_eq_of_pairingIn h2] at hn
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hy hn
  · exact False.elim (hya (Q.root.injective (by simpa using hy)))
  · norm_num at hn
  · have he : y = Q.reflectionPerm c a := Q.root.injective
      (by rw [(b2_roots h1 h2).1]; simpa only [one_smul] using hy)
    subst y
    have htwo := char_two_of_b2_noMixedRoot f hchar hb ha hc hac h1 h2 hcone
    have h := (hd.b2_commRels ha hc hac h1 h2).2
    have hz : PointsCommute (weylFamily Q W u a)
        (wordConj Q u [c] (weylFamily Q W u a)) :=
      pointsCommute_of_commRel_singleton_zero h htwo
    exact pointsCommute_of_word hd (by simpa using hc) (by simp [wordPerm_cons, wordPerm_nil]) hz
  · have ra : Q.root a = (1 : ℤ) • Q.root a + (0 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli ra hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2

include hd in
omit [IsLocalRing R] in
theorem commute_b2_long {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -2) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hyc : y ≠ c)
    (hneg : P.root (f.indexEquiv c) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv c) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u c) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2
    (α := z) (p := v) (q := w) hz
  have hy' : Q.root y = (n : ℤ) • Q.root c + (m : ℤ) • Q.root a := by
    rw [hy, add_comm]
  have hn := nonneg_pairing_combo f hneg hcone hy'
  rw [pairing_eq_of_pairingIn h1] at hn
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hy hn
  · norm_num at hn
  · exact False.elim (hyc (Q.root.injective (by simpa using hy)))
  all_goals
    have rc : Q.root c = (0 : ℤ) • Q.root a + (1 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli rc hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2

include hd hchar hb in
theorem commute_g2_short {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -3) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hya : y ≠ a)
    (hneg : P.root (f.indexEquiv a) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv a) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2
    (α := z) (p := v) (q := w) hz
  have hn := nonneg_pairing_combo f hneg hcone hy
  rw [pairing_eq_of_pairingIn h2] at hn
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2] at hy hn
  · exact False.elim (hya (Q.root.injective (by simpa using hy)))
  · norm_num at hn
  · norm_num at hn
  · have he : y = Q.reflectionPerm a (Q.reflectionPerm c a) := Q.root.injective
      (by rw [(g2_roots h1 h2).2.1]; simpa only [one_smul] using hy)
    subst y
    have hthree := char_three_of_g2_noMixedRoot f hchar hb ha hc hac h1 h2 hcone
    have h := (hd.g2_commRels ha hc hac h1 h2).2.2.1
    have hz : PointsCommute (weylFamily Q W u a)
        (wordConj Q u [a, c] (weylFamily Q W u a)) :=
      pointsCommute_of_commRel_singleton_zero h (by simpa only [neg_eq_zero] using hthree)
    exact pointsCommute_of_word hd (by simp [ha, hc]) (by simp [wordPerm_cons, wordPerm_nil]) hz
  all_goals
    have ra : Q.root a = (1 : ℤ) • Q.root a + (0 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli ra hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2

include hd in
omit [IsLocalRing R] in
theorem commute_g2_long {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c)
    (h1 : Q.pairingIn ℤ a c = -1) (h2 : Q.pairingIn ℤ c a = -3) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hyc : y ≠ c)
    (hneg : P.root (f.indexEquiv c) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv c) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u c) (weylFamily Q W u y) := by
  classical
  have hli := b'.linearIndependent_pair_of_ne
    (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun h => hac (congrArg Subtype.val h))
  have hΦ := fun z v w hz => Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2
    (α := z) (p := v) (q := w) hz
  have hy' : Q.root y = (n : ℤ) • Q.root c + (m : ℤ) • Q.root a := by
    rw [hy, add_comm]
  have hn := nonneg_pairing_combo f hneg hcone hy'
  rw [pairing_eq_of_pairingIn h1] at hn
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (m + n)
      (by push_cast; ring) (by positivity) (by positivity) hy with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2] at hy hn
  · norm_num at hn
  · exact False.elim (hyc (Q.root.injective (by simpa using hy)))
  · have rc : Q.root c = (0 : ℤ) • Q.root a + (1 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli rc hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2
  · have rc : Q.root c = (0 : ℤ) • Q.root a + (1 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli rc hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2
  · norm_num at hn
  · have rc : Q.root c = (0 : ℤ) • Q.root a + (1 : ℤ) • Q.root c := by simp
    have hn' := noOpp_cone_of_coeffs hli rc hy hΦ
      (by norm_num) (by intro s t hs ht h; omega)
    exact hd.pointsCommute hn'.1 hn'.2

include hd hchar hb in
theorem commute_simple_positive {a c y : J'}
    (ha : a ∈ b'.support) (hc : c ∈ b'.support) (hac : a ≠ c) {m n : ℕ}
    (hy : Q.root y = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c)
    (hya : y ≠ a)
    (hneg : P.root (f.indexEquiv a) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv a) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u a) (weylFamily Q W u y) := by
  have hm := Langlands.LinearAlgebra.RootDatumIsogeny.cartanPair_mem_of_simple b' ha hc hac
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hm
  have hy' : Q.root y = (n : ℤ) • Q.root c + (m : ℤ) • Q.root a := by
    rw [hy, add_comm]
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact commute_a1a1 hd ha hc hac h2 hy hya
  · exact commute_a2 f hd ha hc hac h1 h2 hy hya hneg hcone
  · exact commute_b2_short f hd hchar hb ha hc hac h1 h2 hy hya hneg hcone
  · exact commute_b2_long f hd hc ha hac.symm h2 h1 hy' hya hneg hcone
  · exact commute_g2_short f hd hchar hb ha hc hac h1 h2 hy hya hneg hcone
  · exact commute_g2_long f hd hc ha hac.symm h2 h1 hy' hya hneg hcone

include hd hchar hb in
/-- All genuine target Weyl-family maps commute when their corresponding
source roots are not opposite and have no positive integral mixed root. -/
theorem commute_of_normalData {x y : J'}
    (hneg : P.root (f.indexEquiv x) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv x) (f.indexEquiv y)) :
    PointsCommute (weylFamily Q W u x) (weylFamily Q W u y) := by
  classical
  by_cases hxy : x = y
  · subst y
    exact pointsCommute_self _
  have htarget := target_not_opposite f hneg
  have hli : LinearIndependent ℤ ![Q.root x, Q.root y] := by
    by_contra h
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := Q) x y h with he | he
    · exact hxy (Q.root.injective he)
    · exact htarget he
  obtain ⟨l, a, c, hl, ha, hc, hac, hxr, m, n, hyr⟩ :=
    Langlands.LinearAlgebra.exists_word_rankTwo Q b' hli
  obtain ⟨y₀, hyl, hy₀⟩ : ∃ y₀,
      Langlands.LinearAlgebra.wordPerm Q l y₀ = y ∧
      Q.root y₀ = (m : ℤ) • Q.root a + (n : ℤ) • Q.root c :=
    ⟨Langlands.LinearAlgebra.wordPerm Q l.reverse y, wordPerm_reverse l y, by
      rw [Langlands.LinearAlgebra.root_wordPerm, hyr, wordReflect_reverse]⟩
  have hxl : Langlands.LinearAlgebra.wordPerm Q l a = x :=
    Q.root.injective (by rw [Langlands.LinearAlgebra.root_wordPerm, hxr])
  have hya : y₀ ≠ a := by
    intro he
    apply hxy
    rw [← hxl, ← hyl, he]
  have hxs : Langlands.LinearAlgebra.wordPerm P (l.map f.indexEquiv)
      (f.indexEquiv a) = f.indexEquiv x := by
    rw [← indexEquiv_word f, hxl]
  have hys : Langlands.LinearAlgebra.wordPerm P (l.map f.indexEquiv)
      (f.indexEquiv y₀) = f.indexEquiv y := by
    rw [← indexEquiv_word f, hyl]
  have hn := not_opposite_of_word (l.map f.indexEquiv) hxs hys hneg
  have hnc := noMixedRoot_of_word (l.map f.indexEquiv) hxs hys hcone
  have hstd := commute_simple_positive f hd hchar hb ha hc hac hy₀ hya hn hnc
  have hword := pointsCommute_wordConj (D := Q) u l hstd
  have hpx : IsRootParametrization i (Q.root x)
      (wordConj Q u l (weylFamily Q W u a)) := by
    have hp := isRootParametrization_wordConj l
      (fun d hd' => hd.weyl d (hl d hd')) (hd.isRootParametrization a)
    rw [← Langlands.LinearAlgebra.root_wordPerm, hxl] at hp
    exact hp
  have hpy : IsRootParametrization i (Q.root y)
      (wordConj Q u l (weylFamily Q W u y₀)) := by
    have hp := isRootParametrization_wordConj l
      (fun d hd' => hd.weyl d (hl d hd')) (hd.isRootParametrization y₀)
    rw [← Langlands.LinearAlgebra.root_wordPerm, hyl] at hp
    exact hp
  exact pointsCommute_of_rootParametrizations hd.rootDatum hword hpx hpy
    (hd.isRootParametrization x) (hd.isRootParametrization y)

end StandardPairs

section ActualRootMaps

variable {R : Type u} [CommRing R] [IsLocalRing R] [DecidableEq I']
    {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
    (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i)
    (hQ : IsFibrewiseRootDatumOf I' H i Q)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

include hH hi hmax hQ hchar in
/-- Genuine target root maps commute whenever the corresponding
source roots have no positive integral mixed root and are not opposite.
The target cone is allowed to contain exceptional roots. -/
theorem pointsCommute_of_noMixedRoot {x y : J'} {v v' : Ga R ⟶ H}
    (hv : IsRootParametrization i (Q.root x) v)
    (hv' : IsRootParametrization i (Q.root y) v')
    (hneg : P.root (f.indexEquiv x) ≠ -P.root (f.indexEquiv y))
    (hcone : NoMixedRoot P (f.indexEquiv x) (f.indexEquiv y)) :
    PointsCommute v v' := by
  classical
  let C := f.compatibleBases
  obtain ⟨u, hu, hw⟩ :=
    exists_normalizedLocalRootFamily hH i hi hmax hQ C.source
  let W := descWord Q C.source
  have hparam : ∀ a ∈ C.source.support,
      IsRootParametrization i (Q.root a) (u a) ∧
      IsRootParametrization i (Q.root (Q.reflectionPerm a a))
        (u (Q.reflectionPerm a a)) := fun a _ => ⟨hu a, hu _⟩
  have hrank := localSplitRankOneNormal R H hH I' i hi hmax J' Q hQ
    C.source u hparam hw
  have hd : IsNormalSimpleData i Q C.source W u :=
    ⟨hH, hmax, hQ, hparam, hw, isDescendingWords_descWord Q C.source, hrank⟩
  have h := commute_of_normalData f hd hchar
    (fun a ha => (C.simple_iff a).mp ha) hneg hcone
  exact pointsCommute_of_rootParametrizations hQ h
    (hd.isRootParametrization x) (hd.isRootParametrization y) hv hv'

include hH hi hmax hQ hchar in
/-- The same actual-root commutation theorem indexed by the source
roots, in the orientation of the affine isogeny theorem. -/
theorem pointsCommute_correspondingRoots {x y : J} {v v' : Ga R ⟶ H}
    (hv : IsRootParametrization i (Q.root (f.indexEquiv.symm x)) v)
    (hv' : IsRootParametrization i (Q.root (f.indexEquiv.symm y)) v')
    (hneg : P.root x ≠ -P.root y) (hcone : NoMixedRoot P x y) :
    PointsCommute v v' := by
  apply pointsCommute_of_noMixedRoot f hH i hi hmax hQ hchar hv hv'
  · simpa only [Equiv.apply_symm_apply] using hneg
  · simpa only [Equiv.apply_symm_apply] using hcone

end ActualRootMaps

/-- The actual-target no-cone law needed for powered commutator transfer,
including the exceptional characteristic-two and characteristic-three
root cones. -/
def IsogenyNoConeCommutationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (H : GroupScheme (Spec (CommRingCat.of R))) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    haveI := hH.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i →
    ∀ (J J' : Type u) [Finite J] [Finite J']
      (P : RootDatum J (I → ℤ) (I → ℤ))
      (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced],
      IsFibrewiseRootDatumOf I' H i Q →
      ∀ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
        (∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) →
        ∀ (x y : J) (v v' : Ga R ⟶ H),
          IsRootParametrization i (Q.root (f.indexEquiv.symm x)) v →
          IsRootParametrization i (Q.root (f.indexEquiv.symm y)) v' →
          P.root x ≠ -P.root y → NoMixedRoot P x y → PointsCommute v v'

theorem isogenyNoConeCommutation : IsogenyNoConeCommutationStatement.{u} := by
  intro R _ _ H hH I I' _ _ i hi hmax J J' _ _ P Q _ _ hQ p f hchar
    x y v v' hv hv' hneg hcone
  classical
  let : IsAffineHom H.X.hom := hH.isAffineHom
  exact pointsCommute_correspondingRoots f hH i hi hmax hQ hchar hv hv' hneg hcone

end Langlands.GroupScheme.IsogenyNoCone
