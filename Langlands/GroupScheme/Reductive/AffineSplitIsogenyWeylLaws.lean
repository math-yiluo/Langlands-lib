import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWeylActions
import Langlands.GroupScheme.Reductive.LocalSplitTargetWeylLaws
import Langlands.GroupScheme.Reductive.LocalSplitRootPairUniqueness

/-! # Positive Weyl-action laws for the actual powered family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

/-- The source and target Cartan products agree, even when root lengths are exchanged. -/
theorem pairingIn_product_eq (a c : J) :
    P.pairingIn ℤ a c * P.pairingIn ℤ c a =
      Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) *
        Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) := by
  have h₁ := f.rootFactor_mul_pairingIn (f.indexEquiv.symm a) (f.indexEquiv.symm c)
  have h₂ := f.rootFactor_mul_pairingIn (f.indexEquiv.symm c) (f.indexEquiv.symm a)
  simp only [Equiv.apply_symm_apply] at h₁ h₂
  have ha : (f.rootFactor (f.indexEquiv.symm a) : ℤ) ≠ 0 := by
    exact_mod_cast (f.rootFactor_pos (f.indexEquiv.symm a)).ne'
  have hc : (f.rootFactor (f.indexEquiv.symm c) : ℤ) ≠ 0 := by
    exact_mod_cast (f.rootFactor_pos (f.indexEquiv.symm c)).ne'
  apply mul_left_cancel₀ (mul_ne_zero ha hc)
  calc
    _ = ((f.rootFactor (f.indexEquiv.symm a) : ℤ) * P.pairingIn ℤ a c) *
        ((f.rootFactor (f.indexEquiv.symm c) : ℤ) * P.pairingIn ℤ c a) := by ring
    _ = _ := by rw [h₁, h₂]; ring

/-- Conjugation by powered Weyl products is exactly conjugation by the reindexed
genuine target Weyl products, on every additive-line map. -/
theorem wordConj_powered_reindex (u' : J' → (Ga R ⟶ H)) (l : List J)
    (w : Ga R ⟶ H) :
    wordConj P (poweredRootFamily f hchar u') l w =
      wordConj Q u' (l.map f.indexEquiv.symm) w := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change wordConj P (poweredRootFamily f hchar u') l w ≫
      (H.innerIso (rootWeylPoint P (poweredRootFamily f hchar u') c)).hom = _
    rw [ih, rootWeylPoint_poweredRootFamily]
    rfl

/-- Scaling before a root power scales the genuine target parameter by the same power. -/
theorem scaleHom_comp_rootMap (j' : J') (w : Ga R ⟶ H) (k : R) :
    scaleHom k ≫ rootMap f hchar j' w =
      rootMap f hchar j' (scaleHom (k ^ f.rootFactor j') ≫ w) := by
  apply hom_ext_rootPoint
  intro Z x
  simp only [rootPoint_scaleHom, rootPoint_rootMap, mul_pow, map_pow]

/-- The characteristic root powers commute with multiplication by minus one. -/
theorem rootMap_neg_scale (j' : J') (w : Ga R ⟶ H) :
    rootMap f hchar j' (scaleHom (-1 : R) ≫ w) =
      scaleHom (-1 : R) ≫ rootMap f hchar j' w := by
  have hneg : (-1 : R) ^ f.rootFactor j' = -1 := by
    have h := add_pow_rootFactor f hchar j' R (-1) 1
    rw [neg_add_cancel, zero_pow (f.rootFactor_pos j').ne', one_pow] at h
    linear_combination -h
  rw [scaleHom_comp_rootMap, hneg]

/-- Braid, rank-two sign and simple opposite-root identities for the powered family. -/
def PoweredWeylTransportRelations {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) : Prop :=
  let v := poweredRootFamily f hchar u'
  WordBraids P b v ∧
  (∀ c ∈ b.support, ∀ j ∈ b.support, c ≠ j →
    P.pairingIn ℤ c j = -1 → P.pairingIn ℤ j c = -1 →
      wordConj P v [c] (v j) =
        scaleHom ((-1 : Rˣ) : R) ≫ wordConj P v [j] (v c)) ∧
  (∀ a ∈ b.support, ∀ c ∈ b.support, a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -2 →
      wordConj P v [a] (wordConj P v [c] (v a)) =
        scaleHom ((-1 : Rˣ) : R) ≫ wordConj P v [c] (v a)) ∧
  ∀ c ∈ b.support, wordConj P v [c] (weylFamily P W v c) =
    weylFamily P W v (P.reflectionPerm c c)

variable [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom]
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {b : P.Base} {b' : Q.Base}
  (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
  (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
  (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')

include hd

/-- Genuine target braids give the source braids because their lengths and actual
Weyl products agree under the root bijection. -/
theorem wordBraids_poweredRootFamily (hi' : IsClosedSubgroup i') :
    WordBraids P b (poweredRootFamily f hchar u') := by
  have hPU : PartnerUnique Q H i' := by
    intro a xp xm xm' hp hm hm' hn hn'
    exact rootPartner_unique hd.reductive hi' hd.maximal hd.rootDatum a hp hm hm' hn hn'
  have hB := wordBraids_of_partnerUnique hd hPU
  intro c hc j hj hcj w
  have hmap (t : Bool) (n : ℕ) :
      ((altLetters t n).map (letter c j)).map f.indexEquiv.symm =
        (altLetters t n).map (letter (f.indexEquiv.symm c) (f.indexEquiv.symm j)) := by
    rw [List.map_map]
    congr 1
    funext s
    cases s <;> rfl
  rw [wordConj_powered_reindex, wordConj_powered_reindex, hmap, hmap,
    pairingIn_product_eq f]
  exact hB _ (hb c hc) _ (hb j hj)
    (fun h => hcj (f.indexEquiv.symm.injective h)) w

/-- The simple opposite-root bookkeeping is preserved by the exact root powers. -/
theorem wordConj_simple_poweredWeylFamily {c : J} (hc : c ∈ b.support) :
    wordConj P (poweredRootFamily f hchar u') [c]
        (weylFamily P W (poweredRootFamily f hchar u') c) =
      weylFamily P W (poweredRootFamily f hchar u') (P.reflectionPerm c c) := by
  rw [wordConj_weylFamily_powered_eq f hchar hb W u',
    weylFamily_powered_eq f hchar hb W u']
  simp only [List.map_cons, List.map_nil]
  rw [hd.wordConj_weylFamily_simple (hb c hc), f.indexEquiv_symm_reflectionPerm]
  unfold rootMap
  rw [rootPower_eq_of_factor_eq f hchar
    (f.rootFactor_reflectionPerm (f.indexEquiv.symm c) (f.indexEquiv.symm c))]

omit hd [CommRing R] [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom] in
private def scalingPattern {a c : J} (ha : a ∈ b.support)
    (hc : c ∈ b.support) (hac : a ≠ c) :
    Langlands.LinearAlgebra.RootDatumIsogeny.RankTwoScalingPattern
      (Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c))
      (Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a))
      (P.pairingIn ℤ a c) (P.pairingIn ℤ c a)
      (f.rootFactor (f.indexEquiv.symm a)) (f.rootFactor (f.indexEquiv.symm c)) := by
  simpa only [Equiv.apply_symm_apply] using
    f.rankTwoScalingPattern b' b (hb a ha) (hb c hc)
      (fun h => hac (f.indexEquiv.symm.injective h))
      (by simpa only [Equiv.apply_symm_apply] using ha)
      (by simpa only [Equiv.apply_symm_apply] using hc)

/-- The A2 sign identity holds for the actual powered source maps. -/
theorem wordConj_a2_poweredRootFamily {c j : J}
    (hc : c ∈ b.support) (hj : j ∈ b.support) (hcj : c ≠ j)
    (h1 : P.pairingIn ℤ c j = -1) (h2 : P.pairingIn ℤ j c = -1) :
    wordConj P (poweredRootFamily f hchar u') [c] (poweredRootFamily f hchar u' j) =
      scaleHom ((-1 : Rˣ) : R) ≫
        wordConj P (poweredRootFamily f hchar u') [j] (poweredRootFamily f hchar u' c) := by
  cases scalingPattern f hb hc hj hcj with
  | orthogonal _ _ hs1 hs2 => omega
  | equal e1 e2 hq =>
    have ht := hd.wordConj_a2 (hb c hc) (hb j hj)
      (fun h => hcj (f.indexEquiv.symm.injective h)) (e1.trans h1) (e2.trans h2)
    rw [wordConj_poweredRootFamily, wordConj_poweredRootFamily]
    simp only [poweredWordMap, List.map_cons, List.map_nil]
    rw [ht]
    simp only [Units.val_neg, Units.val_one]
    rw [rootMap_neg_scale]
    unfold rootMap
    rw [rootPower_eq_of_factor_eq f hchar hq]
  | doubleForward _ _ hs1 hs2 _ => omega
  | doubleReverse _ _ hs1 hs2 _ => omega
  | tripleForward _ _ hs1 hs2 _ => omega
  | tripleReverse _ _ hs1 hs2 _ => omega

omit hd [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom] in
private theorem b2_powered_of_target {a c : J}
    (ht : wordConj Q u' [f.indexEquiv.symm a]
        (wordConj Q u' [f.indexEquiv.symm c] (u' (f.indexEquiv.symm a))) =
      scaleHom ((-1 : Rˣ) : R) ≫
        wordConj Q u' [f.indexEquiv.symm c] (u' (f.indexEquiv.symm a))) :
    wordConj P (poweredRootFamily f hchar u') [a]
        (wordConj P (poweredRootFamily f hchar u') [c] (poweredRootFamily f hchar u' a)) =
      scaleHom ((-1 : Rˣ) : R) ≫
        wordConj P (poweredRootFamily f hchar u') [c] (poweredRootFamily f hchar u' a) := by
  change wordConj P (poweredRootFamily f hchar u') [a]
      (wordConj P (poweredRootFamily f hchar u') [c]
        (rootMap f hchar (f.indexEquiv.symm a) (u' (f.indexEquiv.symm a)))) = _
  rw [wordConj_rootMap, wordConj_rootMap, wordConj_poweredRootFamily]
  simp only [List.map_cons, List.map_nil, poweredWordMap]
  rw [ht]
  simp only [Units.val_neg, Units.val_one]
  exact rootMap_neg_scale f hchar _ _

/-- The B2 sign identity also holds when the target root lengths are exchanged:
the fixed genuine target map acquires the required sign in characteristic two. -/
theorem wordConj_b2_poweredRootFamily {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    wordConj P (poweredRootFamily f hchar u') [a]
        (wordConj P (poweredRootFamily f hchar u') [c] (poweredRootFamily f hchar u' a)) =
      scaleHom ((-1 : Rˣ) : R) ≫
        wordConj P (poweredRootFamily f hchar u') [c] (poweredRootFamily f hchar u' a) := by
  classical
  apply b2_powered_of_target f hchar u'
  cases scalingPattern f hb ha hc hac with
  | orthogonal _ _ hs1 hs2 => omega
  | equal e1 e2 _ =>
    exact hd.wordConj_b2 (hb a ha) (hb c hc)
      (fun h => hac (f.indexEquiv.symm.injective h)) (e1.trans h1) (e2.trans h2)
  | doubleForward _ _ hs1 hs2 _ => omega
  | doubleReverse e1 e2 _ _ hratio =>
    let A := f.indexEquiv.symm a
    let C := f.indexEquiv.symm c
    have hA := hb a ha
    have hC := hb c hc
    have hAC : A ≠ C := fun h => hac (f.indexEquiv.symm.injective h)
    have hroot : Q.root (Q.reflectionPerm C A) =
        (1 : ℤ) • Q.root A + (2 : ℤ) • Q.root C := by
      rw [root_reflectionPerm_eq, pairing_eq_of_pairingIn e1]
      module
    have hp0 : Q.pairingIn ℤ (Q.reflectionPerm C A) A = 0 := by
      rw [pairingIn_eq_pairing, pairing_combo (a := A) (c := C) hroot A,
        RootPairing.pairing_same, pairing_eq_of_pairingIn e2]
      norm_num
    have hw := hd.isRootParametrization_wordConj (l := [C]) (by simpa using hC)
      (hd.param A hA).1
    have hfix := hd.wordConj_fix_of_coeffs hA hC hAC hw hp0 hroot
      (Φ := fun m n => (n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) ∨
        (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 1) ∨
        (n = -1 ∧ m = 0) ∨ (n = 0 ∧ m = -1) ∨
        (n = -1 ∧ m = -1) ∨ (n = -2 ∧ m = -1))
      (fun g m n h => Langlands.LinearAlgebra.b2_coeffs hC hA hAC.symm e2 e1
        (by rw [h, add_comm]))
      (by omega) (fun dS dT hdS hdT h => by omega)
      (by omega) (fun dS dT hdS hdT h => by omega)
    have hp : p = 2 :=
      f.characteristicExponent_eq_of_rootFactor_ratio Nat.prime_two C A hratio
    have h₂ : (2 : R) = 0 := by
      have hq := f.rootFactor_pos C
      have hne : f.rootFactor A ≠ 1 := by change f.rootFactor A = 2 * f.rootFactor C at hratio; omega
      simpa only [hp, Nat.cast_ofNat] using hchar A hne
    have hneg : (-1 : R) = 1 := by linear_combination -h₂
    simpa only [Units.val_neg, Units.val_one, hneg, scaleHom_one, Category.id_comp]
      using hfix
  | tripleForward _ _ hs1 hs2 _ => omega
  | tripleReverse _ _ hs1 hs2 _ => omega

/-- All four transport identities follow from genuine normalized target data. -/
theorem poweredWeylTransportRelations (hi' : IsClosedSubgroup i') :
    PoweredWeylTransportRelations f hchar W u' := by
  refine ⟨wordBraids_poweredRootFamily f hchar hb W u' hd hi', ?_, ?_, ?_⟩
  · intro c hc j hj hcj h1 h2
    exact wordConj_a2_poweredRootFamily f hchar hb W u' hd hc hj hcj h1 h2
  · intro a ha c hc hac h1 h2
    exact wordConj_b2_poweredRootFamily f hchar hb W u' hd ha hc hac h1 h2
  · intro c hc
    exact wordConj_simple_poweredWeylFamily f hchar hb W u' hd hc

end Langlands.GroupScheme.AffineRootDatumIsogeny
