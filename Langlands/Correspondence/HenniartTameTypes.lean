import Langlands.Correspondence.HenniartUnramified.Strata
import Langlands.Representation.Clifford.Classes
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# Frobenius-fixed inertia types and the conductor counts

The conductor count `C_F(k + 1, j)` of a p-adic field `F` equals the number of isomorphism
classes of continuous irreducible representations of inertia that are fixed by conjugation by a
degree-one Weil element, have rank dividing `k + 1` and break at most `j / (k + 1)`.
-/

noncomputable section

namespace Langlands.Henniart.TameTypes

open Weil.Local FiniteRepresentation FiniteRepresentation.SplitDegree Numerical
open VirtualRepresentation VirtualRepresentation.LocalWeil.Ramification Correspondence

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Conjugation by a Weil element, as a continuous automorphism of inertia. -/
def frobConj (φ : localWeilGroup F) : localInertia F ≃ₜ* localInertia F where
  toFun g := ⟨φ * g * φ⁻¹, (localInertia_normal F).conj_mem _ g.2 φ⟩
  invFun g := ⟨φ⁻¹ * g * φ, by
    have h := (localInertia_normal F).conj_mem _ g.2 φ⁻¹
    rwa [inv_inv] at h⟩
  left_inv g := by
    apply Subtype.ext
    change φ⁻¹ * (φ * (g : localWeilGroup F) * φ⁻¹) * φ = g
    group
  right_inv g := by
    apply Subtype.ext
    change φ * (φ⁻¹ * (g : localWeilGroup F) * φ) * φ⁻¹ = g
    group
  map_mul' x y := by
    apply Subtype.ext
    change φ * ((x : localWeilGroup F) * y) * φ⁻¹ = (φ * x * φ⁻¹) * (φ * y * φ⁻¹)
    group
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

@[simp] theorem frobConj_apply (φ : localWeilGroup F) (g : localInertia F) :
    ((frobConj F φ g : localInertia F) : localWeilGroup F) = φ * g * φ⁻¹ := rfl

variable (φ : localWeilGroup F) (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ))

/-- Pullback along conjugation by `φ` is the Frobenius conjugation of the split degree
data. -/
theorem typePullback_frobConj (x : Clifford.TypeClasses.{uF, uW} (localInertia F)) :
    Clifford.typePullback (frobConj F φ) x = (weilSplit F φ hφ).conjType 1 x := by
  induction x using Quotient.inductionOn with
  | h B =>
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    change B.1.representation (frobConj F φ n) = B.1.representation ((weilSplit F φ hφ).cj 1 n)
    congr 1
    apply Subtype.ext
    change φ * (n : localWeilGroup F) * φ⁻¹ =
      (weilSplit F φ hφ).lift ^ 1 * (n : localWeilGroup F) * ((weilSplit F φ hφ).lift ^ 1)⁻¹
    rw [pow_one]


/-- The rank of a type class. -/
def typeRank : Clifford.TypeClasses.{uF, uW} (localInertia F) → ℕ :=
  Quotient.lift (fun B => Module.finrank ℂ B.1) fun _ _ ⟨e⟩ => e.toLinearEquiv.finrank_eq

/-- The break of a type class. -/
def typeBreak : Clifford.TypeClasses.{uF, uW} (localInertia F) → ℝ :=
  Quotient.lift (fun B => inertiaBreak F B.1.representation) fun _ _ ⟨e⟩ =>
    inertiaBreak_equiv F e

theorem typeRank_mk (B : Clifford.TypeObj.{uF, uW} (localInertia F)) :
    typeRank F (Clifford.typeClass B) = Module.finrank ℂ B.1 := rfl

theorem typeBreak_mk (B : Clifford.TypeObj.{uF, uW} (localInertia F)) :
    typeBreak F (Clifford.typeClass B) = inertiaBreak F B.1.representation := rfl

include hφ in
/-- For `φ` of degree one and a type fixed by conjugation by `φ`, the rank times the break is a
natural number and some upper group of nonnegative index acts trivially on the type. (The type
extends to an irreducible Weil representation, whose Swan label gives the first assertion.) -/
theorem exists_nat_of_fixed (B : Clifford.TypeObj.{uF, uW} (localInertia F))
    (hB : Clifford.typePullback (frobConj F φ) (Clifford.typeClass B) = Clifford.typeClass B) :
    (∃ s : ℕ, ((Module.finrank ℂ B.1 : ℕ) : ℝ) * inertiaBreak F B.1.representation = s) ∧
      ∃ v : ℝ, 0 ≤ v ∧ ∀ n : localInertia F, (n : localWeilGroup F) ∈ upperGroup F v →
        B.1.representation n = 1 := by
  rw [typePullback_frobConj F φ hφ] at hB
  have hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = 0 + 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hB
  let S := weilStage F φ hφ 0
  let AL : WeilObj.{uF, uW} F := ⟨FiniteRepresentation.of (S.typeCoind B hp),
    S.typeCoind_continuous B hp, S.typeCoind_isIrreducible B hp⟩
  have : Nontrivial B.1 := nontrivial_of_isIrreducible _ B.2.2
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℂ) (M := B.1)).ne'
  have hAL : AL.1.rank = r' + 1 := by
    change Module.finrank ℂ (Fin (0 + 1) → B.1) = r' + 1
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [zero_add, one_mul]
    exact hr'
  have hl := (hasWeilSwan_iff_eq_label F (weilClassOf F AL hAL) _).mpr rfl
  have h1 := (hasWeilSwan_weilClassOf F AL hAL _).mp hl
  have h2 : lastBreak F AL.1 = inertiaBreak F B.1.representation := lastBreak_typeCoind F φ hφ S B hp
  refine ⟨⟨weilSwanLabel F (weilClassOf F AL hAL), ?_⟩, ?_⟩
  · rw [h1, h2, hr']
  · obtain ⟨v, hv0, hv⟩ := Ramification.HerbrandBridge.weilTrivialityThresholdsNonempty F AL.1 AL.2.1
    refine ⟨v, hv0, ?_⟩
    have h3 := (S.typeCoind_trivial_iff B hp (upperGroup F v)).mp
      (fun n hn => hv (n : localWeilGroup F) hn)
    exact h3

include hφ in
/-- For `φ` of degree one, a type class fixed by conjugation by `φ` has rank times break a
natural number. -/
theorem exists_nat_of_fixed_class (x : Clifford.TypeClasses.{uF, uW} (localInertia F))
    (hx : Clifford.typePullback (frobConj F φ) x = x) :
    ∃ s : ℕ, (typeRank F x : ℝ) * typeBreak F x = s := by
  induction x using Quotient.inductionOn with
  | h B => exact (exists_nat_of_fixed F φ hφ B hx).1

/-- The Frobenius-fixed type classes of rank `d` with `d · break = s`. -/
def fixedStratum (d s : ℕ) : Set (Clifford.TypeClasses.{uF, uW} (localInertia F)) :=
  {x | Clifford.typePullback (frobConj F φ) x = x ∧ typeRank F x = d ∧
    (d : ℝ) * typeBreak F x = s}

include hφ in
/-- For `φ` of degree one and `d > 0`, `weilTwistIrreducibleCount F (d - 1) s` (Henniart's
`T_F(d, s)`) is the number of type classes fixed by conjugation by `φ` of rank `d` with
`d · break = s`. -/
theorem weilTwistIrreducibleCount_eq (d s : ℕ) (hd : 0 < d) :
    weilTwistIrreducibleCount.{uF, uW} F (d - 1) s = (fixedStratum.{uF, uW} F φ d s).encard := by
  have h := encard_period_goodTypes (F := F) (φ := φ) (hφ := hφ) (d - 1) s 0 d s
    (by omega) (by ring)
  have hset : {x ∈ goodTypes.{uF, uW} F φ hφ d s |
      Function.minimalPeriod ((weilSplit F φ hφ).conjType 1) x = 0 + 1} =
      fixedStratum.{uF, uW} F φ d s := by
    ext x
    induction x using Quotient.inductionOn with
    | h B =>
      constructor
      · rintro ⟨⟨B', hB', hgood⟩, hper⟩
        obtain ⟨e⟩ := (Clifford.typeClass_eq_iff _ _).mp hB'
        have hgood' := (typeGood_congr e).mp hgood
        refine ⟨?_, hgood'.1, hgood'.2⟩
        exact (typePullback_frobConj F φ hφ (Clifford.typeClass B)).trans
          (Function.minimalPeriod_eq_one_iff_isFixedPt.mp hper)
      · rintro ⟨hfix, hrank, hbreak⟩
        refine ⟨⟨B, rfl, hrank, hbreak⟩, ?_⟩
        exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr
          ((typePullback_frobConj F φ hφ (Clifford.typeClass B)).symm.trans hfix)
  rw [hset] at h
  calc weilTwistIrreducibleCount.{uF, uW} F (d - 1) s
      = (weilRefinedStratum.{uF, uW} F (d - 1) s 1).encard := rfl
    _ = (weilRefinedStratum.{uF, uW} F (d - 1) s (0 + 1)).encard * ((0 + 1 : ℕ) : ℕ∞) := by
        simp
    _ = _ := h.symm

omit [Fact p.Prime] in
theorem encard_biUnion_finset {ι α : Type*} [DecidableEq ι] (t : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ t, S i).encard = ∑ i ∈ t, (S i).encard := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hd : Disjoint (S a) (⋃ i ∈ t, S i) := by
      refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
      exact h a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq hd, ih]
    intro i hi j hj hij
    exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

include hφ in
/-- For `φ` of degree one, the conductor count `C_F(k + 1, j)` is the number of type classes fixed
by conjugation by `φ` of rank dividing `k + 1` with `(k + 1) · break ≤ j`. -/
theorem weilConductorCount_eq (k j : ℕ) :
    weilConductorCount.{uF, uW} F k j =
      {x : Clifford.TypeClasses.{uF, uW} (localInertia F) |
        Clifford.typePullback (frobConj F φ) x = x ∧ typeRank F x ∣ k + 1 ∧
          ((k + 1 : ℕ) : ℝ) * typeBreak F x ≤ j}.encard := by
  classical
  unfold weilConductorCount
  have h1 : ∀ d ∈ (k + 1).divisors,
      ∑ s ∈ Finset.range (d * j / (k + 1) + 1), weilTwistIrreducibleCount.{uF, uW} F (d - 1) s =
        (⋃ s ∈ Finset.range (d * j / (k + 1) + 1), fixedStratum.{uF, uW} F φ d s).encard := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [encard_biUnion_finset]
    · exact Finset.sum_congr rfl fun s _ => weilTwistIrreducibleCount_eq F φ hφ d s hd0
    · intro s _ s' _ hss'
      refine Set.disjoint_left.mpr fun x hx hx' => hss' ?_
      exact_mod_cast hx.2.2.symm.trans hx'.2.2
  rw [Finset.sum_congr rfl h1, ← encard_biUnion_finset]
  · congr 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨d, hd, s, hs, hfix, hrank, hbreak⟩
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      refine ⟨hfix, hrank ▸ Nat.dvd_of_mem_divisors hd, ?_⟩
      have hs' : s * (k + 1) ≤ d * j := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mp
        (Nat.lt_succ_iff.mp hs)
      have hs'' : (s : ℝ) * (k + 1) ≤ d * j := by exact_mod_cast hs'
      rw [← hbreak] at hs''
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
      have : (d : ℝ) * (((k + 1 : ℕ) : ℝ) * typeBreak F x) ≤ d * j := by
        push_cast
        linarith
      exact le_of_mul_le_mul_left this hdpos
    · rintro ⟨hfix, hdvd, hbreak⟩
      obtain ⟨s, hs⟩ := exists_nat_of_fixed_class F φ hφ x hfix
      refine ⟨typeRank F x, Nat.mem_divisors.mpr ⟨hdvd, Nat.succ_ne_zero k⟩, s, ?_, hfix, rfl, hs⟩
      apply Nat.lt_succ_iff.mpr
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr
      have hb0 : (0 : ℝ) ≤ typeRank F x := Nat.cast_nonneg _
      have : (s : ℝ) * (k + 1) ≤ typeRank F x * j := by
        rw [← hs]
        have h2 := mul_le_mul_of_nonneg_left hbreak hb0
        push_cast at h2
        linarith
      exact_mod_cast this
  · intro d _ d' _ hdd'
    refine Set.disjoint_left.mpr fun x hx hx' => hdd' ?_
    simp only [Set.mem_iUnion] at hx hx'
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨s', _, hx'⟩ := hx'
    exact hx.2.1.symm.trans hx'.2.1

end Langlands.Henniart.TameTypes
