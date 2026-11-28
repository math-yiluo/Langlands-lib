import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # The three line parabolics of a root datum of type A₂ -/

universe u v w

namespace Langlands.LinearAlgebra

open Matrix

/-- The six coroots in terms of the two simple coroots of an `A₂` system. -/
def a2Coroots {Y : Type*} [AddCommGroup Y] (a b : Y) : Fin 6 → Y :=
  ![a, b, a + b, -a, -b, -(a + b)]

/-- An additive equivalence carries the six-coroot list to the corresponding list. -/
theorem map_a2Coroots {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A ≃+ B) (a b : A) (k : Fin 6) :
    f (a2Coroots a b k) = a2Coroots (f a) (f b) k := by
  fin_cases k <;> simp [a2Coroots]

/-- Integral cocharacters for the three coordinate line parabolics. -/
def a2ParabolicCocharacters {Y : Type*} [AddCommGroup Y] (a b : Y) : Fin 3 → Y :=
  ![(2 : ℤ) • a + b, -a + b, -a - (2 : ℤ) • b]

variable {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum I X Y) (a b : I)

private def a2PairingTable : Fin 6 → ℤ × ℤ :=
  ![(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)]

private theorem exists_a2_pairings
    (hab : P.pairing a b = -1) (hba : P.pairing b a = -1)
    (hcase : ∀ i, ∃ j, P.coroot i = a2Coroots (P.coroot a) (P.coroot b) j) (i : I) :
    ∃ j, (P.root' i (P.coroot a), P.root' i (P.coroot b)) = a2PairingTable j := by
  let c := P.reflectionPerm a b
  let opp := fun k : I => P.reflectionPerm k k
  have hc : P.coroot c = P.coroot a + P.coroot b := by
    rw [show c = P.reflectionPerm a b from rfl, P.coroot_reflectionPerm,
      P.coreflection_apply_coroot, hab, neg_one_smul, sub_neg_eq_add, add_comm]
  have hr : P.root c = P.root a + P.root b := by
    rw [show c = P.reflectionPerm a b from rfl, P.root_reflectionPerm,
      P.reflection_apply_root, hba, neg_one_smul, sub_neg_eq_add, add_comm]
  have hcopp (k : I) : P.coroot (opp k) = -P.coroot k := by
    rw [show opp k = P.reflectionPerm k k from rfl, P.coroot_reflectionPerm,
      P.coreflection_apply_self]
  have hropp (k : I) : P.root (opp k) = -P.root k := by
    rw [show opp k = P.reflectionPerm k k from rfl, P.root_reflectionPerm,
      P.reflection_apply_self]
  obtain ⟨j, hj⟩ := hcase i
  refine ⟨j, ?_⟩
  let indices : Fin 6 → I := ![a, b, c, opp a, opp b, opp c]
  have hindices (j : Fin 6) : P.coroot (indices j) =
      a2Coroots (P.coroot a) (P.coroot b) j := by
    fin_cases j <;> simp [indices, a2Coroots, hc, hcopp]
  rw [P.coroot.injective (hj.trans (hindices j).symm)]
  change (P.toLinearMap (P.root (indices j)) (P.coroot a),
    P.toLinearMap (P.root (indices j)) (P.coroot b)) = _
  fin_cases j <;> simp [indices, a2PairingTable, hr, hropp,
    show P.toLinearMap (P.root a) (P.coroot a) = 2 from P.pairing_same a,
    show P.toLinearMap (P.root b) (P.coroot b) = 2 from P.pairing_same b,
    show P.toLinearMap (P.root a) (P.coroot b) = -1 from hab,
    show P.toLinearMap (P.root b) (P.coroot a) = -1 from hba]

private theorem a2PairingTable_negative_and_regular : ∀ j : Fin 6,
    (∃! k : Fin 3, a2ParabolicCocharacters (a2PairingTable j).1 (a2PairingTable j).2 k < 0) ∧
    a2ParabolicCocharacters (a2PairingTable j).1 (a2PairingTable j).2 0 -
      a2ParabolicCocharacters (a2PairingTable j).1 (a2PairingTable j).2 1 ≠ 0 := by
  unfold ExistsUnique
  decide

/-- Each root is negative on exactly one of the three cocharacters, and the
first difference is regular. -/
theorem a2ParabolicCocharacters_negative_and_regular
    (hab : P.pairing a b = -1) (hba : P.pairing b a = -1)
    (hcase : ∀ i, ∃ j, P.coroot i = a2Coroots (P.coroot a) (P.coroot b) j) (i : I) :
    (∃! k : Fin 3, P.root' i (a2ParabolicCocharacters (P.coroot a) (P.coroot b) k) < 0) ∧
    P.root' i (a2ParabolicCocharacters (P.coroot a) (P.coroot b) 0 -
      a2ParabolicCocharacters (P.coroot a) (P.coroot b) 1) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_a2_pairings P a b hab hba hcase i
  have he (k : Fin 3) :
      P.root' i (a2ParabolicCocharacters (P.coroot a) (P.coroot b) k) =
      a2ParabolicCocharacters (P.root' i (P.coroot a)) (P.root' i (P.coroot b)) k := by
    fin_cases k <;> simp [a2ParabolicCocharacters]
  simp only [map_sub, he]
  exact congrArg (fun z : ℤ × ℤ =>
    (∃! k : Fin 3, a2ParabolicCocharacters z.1 z.2 k < 0) ∧
    a2ParabolicCocharacters z.1 z.2 0 - a2ParabolicCocharacters z.1 z.2 1 ≠ 0) hj ▸
    a2PairingTable_negative_and_regular j

/-- The three cocharacters have sum zero. -/
theorem a2ParabolicCocharacters_sum {Y' : Type*} [AddCommGroup Y'] (a b : Y') :
    a2ParabolicCocharacters a b 0 + a2ParabolicCocharacters a b 1 +
      a2ParabolicCocharacters a b 2 = 0 := by
  change ((2 : ℤ) • a + b) + (-a + b) + (-a - (2 : ℤ) • b) = 0
  abel

/-- The first cocharacter is obtained from each of the other two by Weyl
reflections. -/
theorem exists_weyl_coweightEquiv_a2ParabolicCocharacters
    (hab : P.pairing a b = -1) (hba : P.pairing b a = -1) (k : Fin 3) :
    ∃ w : P.Aut, w ∈ P.weylGroup ∧
      w.coweightEquiv (a2ParabolicCocharacters (P.coroot a) (P.coroot b) k) =
        a2ParabolicCocharacters (P.coroot a) (P.coroot b) 0 := by
  let sa := RootPairing.Equiv.reflection P a
  let sb := RootPairing.Equiv.reflection P b
  let ν := a2ParabolicCocharacters (P.coroot a) (P.coroot b)
  have ha : sa.coweightEquiv (ν 1) = ν 0 := by
    change P.coreflection a (ν 1) = ν 0
    have he : P.root' a (ν 1) = -3 := by
      simp [ν, a2ParabolicCocharacters, show P.root' a (P.coroot a) = 2 from P.pairing_same a,
        show P.root' a (P.coroot b) = -1 from hab]
    rw [P.coreflection_apply, he]
    simp only [ν, a2ParabolicCocharacters, cons_val_zero, cons_val_one]
    abel
  have hb : sb.coweightEquiv (ν 2) = ν 1 := by
    change P.coreflection b (ν 2) = ν 1
    have he : P.root' b (ν 2) = -3 := by
      simp [ν, a2ParabolicCocharacters, show P.root' b (P.coroot b) = 2 from P.pairing_same b,
        show P.root' b (P.coroot a) = -1 from hba]
    rw [P.coreflection_apply, he]
    change -P.coroot a - (2 : ℤ) • P.coroot b - (-3 : ℤ) • P.coroot b =
      -P.coroot a + P.coroot b
    abel
  fin_cases k
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨sa, P.reflection_mem_weylGroup _, ha⟩
  · refine ⟨sb * sa, mul_mem (P.reflection_mem_weylGroup _) (P.reflection_mem_weylGroup _), ?_⟩
    change sa.coweightEquiv (sb.coweightEquiv (ν 2)) = ν 0
    rw [hb, ha]

private theorem corootSpan_eq_span_pair
    (hcase : ∀ i, ∃ j, P.coroot i = a2Coroots (P.coroot a) (P.coroot b) j) :
    P.corootSpan ℤ = Submodule.span ℤ (Set.range ![P.coroot a, P.coroot b]) := by
  let L := Submodule.span ℤ (Set.range ![P.coroot a, P.coroot b])
  have ha : P.coroot a ∈ L := Submodule.subset_span ⟨0, rfl⟩
  have hb : P.coroot b ∈ L := Submodule.subset_span ⟨1, rfl⟩
  change Submodule.span ℤ (Set.range P.coroot) = L
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hcase i
    rw [hj]
    have hab := L.add_mem ha hb
    fin_cases j
    · exact ha
    · exact hb
    · exact hab
    · exact L.neg_mem ha
    · exact L.neg_mem hb
    · exact L.neg_mem hab
  · apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩

/-- A base-preserving automorphism with cube one fixes the coroot span of
an `A₂` system, since its permutation of the at most two simple coroots is trivial. -/
theorem coweightEquiv_eq_self_of_a2_of_cube_eq_one
    (hcase : ∀ i, ∃ j, P.coroot i = a2Coroots (P.coroot a) (P.coroot b) j)
    (B : P.Base) (x : P.Aut) (hx : ∀ i, i ∈ B.support ↔ x.indexEquiv i ∈ B.support)
    (h3 : x ^ 3 = 1) (ν : Y) (hν : ν ∈ P.corootSpan ℤ) : x.coweightEquiv ν = ν := by
  classical
  have hspan : Submodule.span ℤ (Set.range (fun i : B.support => P.coroot i)) = P.corootSpan ℤ := by
    change Submodule.span ℤ (Set.range (fun i : (B.support : Set I) => P.coroot i)) =
      Submodule.span ℤ (Set.range P.coroot)
    rw [← Set.image_eq_range (⇑P.coroot) (B.support : Set I)]
    exact B.span_int_coroot_support
  have hcard : Fintype.card B.support ≤ 2 := by
    have hli : LinearIndependent ℤ (fun i : B.support => P.coroot i) :=
      B.linearIndepOn_coroot
    calc
      Fintype.card B.support =
          Module.finrank ℤ (Submodule.span ℤ (Set.range (fun i : B.support => P.coroot i))) :=
        (finrank_span_eq_card hli).symm
      _ = Module.finrank ℤ (Submodule.span ℤ (Set.range ![P.coroot a, P.coroot b])) := by
        rw [hspan, corootSpan_eq_span_pair P a b hcase]
      _ ≤ 2 := (finrank_range_le_card (R := ℤ) ![P.coroot a, P.coroot b]).trans_eq
        (Fintype.card_fin 2)
  let π : Equiv.Perm B.support := Equiv.subtypeEquiv x.indexEquiv hx
  have hπ3 : π ^ 3 = 1 := by
    ext i
    have h := congrArg (fun z : P.Aut => z.indexEquiv i.val) h3
    simpa [pow_succ, RootPairing.Equiv.mul_eq_comp, π] using h
  have hπsq : π ^ 2 = 1 := by
    have hn : Fintype.card (Equiv.Perm B.support) ∣ 2 := by
      rw [Fintype.card_perm]
      interval_cases Fintype.card B.support <;> decide
    obtain ⟨m, hm⟩ := hn
    rw [hm, pow_mul, pow_card_eq_one, one_pow]
  have hπ : π = 1 := by rwa [pow_succ, hπsq, one_mul] at hπ3
  let f : Y →ₗ[ℤ] Y := x.coweightEquiv.toLinearMap - LinearMap.id
  have hle : P.corootSpan ℤ ≤ f.ker := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have he : x.indexEquiv i.val = i.val :=
      congrArg (fun p : Equiv.Perm B.support => (p i).val) hπ
    have hh := RootPairing.Hom.coroot_coweightMap_apply P P (x.indexEquiv i.val) x.toHom
    rw [Equiv.symm_apply_apply, he] at hh
    apply LinearMap.mem_ker.mpr
    change x.coweightEquiv (P.coroot i) - P.coroot i = 0
    exact sub_eq_zero.mpr hh
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hle hν))

end Langlands.LinearAlgebra
