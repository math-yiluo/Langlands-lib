import Langlands.GroupTheory.HeightFiltration

/-! # Successive quotients of finite height filtrations -/

noncomputable section

universe v

open scoped commutatorElement

namespace Langlands.GroupTheory.HeightLayer

open HeightFiltration
open Langlands.GroupScheme.RelativeRoot.CentralExtension

variable {G : Type v} [Group G] {n : ℕ}

/-- Retain exactly the factors at the specified height. -/
def exactFactor (H : Fin n → Subgroup G) (w : Fin n → ℕ) (d : ℕ) (i : Fin n) :
    Subgroup G :=
  ⨆ (_ : w i = d), H i

variable (H : Fin n → Subgroup G) (w : Fin n → ℕ)

theorem exactFactor_of_eq {d : ℕ} {i : Fin n} (h : w i = d) :
    exactFactor H w d i = H i :=
  iSup_pos h

theorem exactFactor_of_ne {d : ℕ} {i : Fin n} (h : w i ≠ d) :
    exactFactor H w d i = ⊥ :=
  iSup_neg h

theorem exactFactor_le (d : ℕ) (i : Fin n) : exactFactor H w d i ≤ H i :=
  iSup_le fun _ => le_rfl

theorem exactFactor_le_level (d : ℕ) (i : Fin n) :
    exactFactor H w d i ≤ level H w d :=
  iSup_le fun hi => le_level H w (Nat.le_of_eq hi.symm)

variable
    (hc : ∀ i j, ⁅H i, H j⁆ ≤ level H w (w i + w j))

/-- The successive quotient at one height, with its sum-bound witness retained. -/
def Layer (_hc : ∀ i j, ⁅H i, H j⁆ ≤ level H w (w i + w j)) (d : ℕ) : Type v :=
  level H w d ⧸ (level H w (d + 1)).subgroupOf (level H w d)

instance layerGroup (d : ℕ) : Group (Layer H w hc d) := by
  letI := normal_next H w hc d
  exact inferInstanceAs
    (Group (level H w d ⧸ (level H w (d + 1)).subgroupOf (level H w d)))

/-- The quotient homomorphism from a height subgroup to its next layer. -/
def projection (d : ℕ) :
    level H w d →* Layer H w hc d := by
  letI := normal_next H w hc d
  exact QuotientGroup.mk' _

theorem projection_eq_one_iff (d : ℕ) (a : level H w d) :
    projection H w hc d a = 1 ↔ (a : G) ∈ level H w (d + 1) := by
  let := normal_next H w hc d
  exact QuotientGroup.eq_one_iff a

theorem projection_surjective (d : ℕ) :
    Function.Surjective (projection H w hc d) := by
  let := normal_next H w hc d
  exact QuotientGroup.mk'_surjective _

/-- The map of one exact-height factor into the successive quotient. -/
def coordinateMap (d : ℕ) (i : Fin n) :
    exactFactor H w d i →* Layer H w hc d :=
  (projection H w hc d).comp (Subgroup.inclusion (exactFactor_le_level H w d i))

theorem coordinateMap_commute {d : ℕ} (hd : 0 < d) (i j : Fin n)
    (a : exactFactor H w d i) (b : exactFactor H w d j) :
    Commute (coordinateMap H w hc d i a) (coordinateMap H w hc d j b) := by
  have hcomm : ⁅exactFactor H w d i, exactFactor H w d j⁆ ≤ level H w (d + 1) := by
    by_cases hi : w i = d
    · by_cases hj : w j = d
      · rw [exactFactor_of_eq H w hi, exactFactor_of_eq H w hj]
        exact (hc i j).trans (antitone_level H w (by omega))
      · rw [exactFactor_of_ne H w hj, Subgroup.commutator_bot_right]
        exact bot_le
    · rw [exactFactor_of_ne H w hi, Subgroup.commutator_bot_left]
      exact bot_le
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅projection H w hc d _, projection H w hc d _⁆ = 1
  rw [← map_commutatorElement]
  apply (projection_eq_one_iff H w hc d _).mpr
  exact hcomm (Subgroup.commutator_mem_commutator a.property b.property)

private theorem prod_map_mul_of_commute {M : Type v} [Monoid M] {I : Type*}
    (a b : I → M) (hc' : ∀ i j, Commute (b i) (a j)) (l : List I) :
    (l.map (fun i => a i * b i)).prod =
      (l.map a).prod * (l.map b).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      have hcomm : Commute (b i) (l.map a).prod :=
        Commute.list_prod_right _ _ (by
          intro x hx
          obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
          exact hc' i j)
      calc
        (a i * b i) * ((l.map a).prod * (l.map b).prod) =
            a i * (b i * (l.map a).prod) * (l.map b).prod := by
              simp only [mul_assoc]
        _ = a i * ((l.map a).prod * b i) * (l.map b).prod := by rw [hcomm.eq]
        _ = (a i * (l.map a).prod) * (b i * (l.map b).prod) := by
              simp only [mul_assoc]

/-- Multiplication of the exact-height coordinates in the quotient. -/
def layerMap (d : ℕ) (hd : 0 < d) :
    (∀ i, exactFactor H w d i) →* Layer H w hc d where
  toFun := orderedProduct (coordinateMap H w hc d)
  map_one' := by
    simp only [orderedProduct, Pi.one_apply, map_one, List.ofFn_const,
      List.prod_replicate, one_pow]
  map_mul' a b := by
    simp only [orderedProduct, Pi.mul_apply, map_mul]
    simpa only [List.map_ofFn, Function.comp_def, id_eq] using
      prod_map_mul_of_commute
        (fun i => coordinateMap H w hc d i (a i))
        (fun i => coordinateMap H w hc d i (b i))
        (fun i j => coordinateMap_commute H w hc hd i j (b i) (a j))
        (List.ofFn id)

/-- The same ordered product, viewed as an element of the height subgroup. -/
def productInLevel (d : ℕ) (a : ∀ i, exactFactor H w d i) : level H w d :=
  ⟨orderedProduct (fun i => (exactFactor H w d i).subtype) a,
    (level H w d).list_prod_mem (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact exactFactor_le_level H w d i (a i).property)⟩

theorem layerMap_eq_projection (d : ℕ) (hd : 0 < d)
    (a : ∀ i, exactFactor H w d i) :
    layerMap H w hc d hd a = projection H w hc d (productInLevel H w d a) := by
  change (List.ofFn fun i => coordinateMap H w hc d i (a i)).prod = _
  let b : Fin n → level H w d := fun i =>
    Subgroup.inclusion (exactFactor_le_level H w d i) (a i)
  have hb : (List.ofFn b).prod = productInLevel H w d a := by
    apply Subtype.ext
    change (level H w d).subtype ((List.ofFn b).prod) = _
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [← hb, map_list_prod, List.map_ofFn]
  rfl

/-- Unique full ordered coordinates imply injectivity in each positive layer. -/
theorem layerMap_injective
    (hw : ∀ i, 0 < w i)
    (hu : Function.Injective (orderedProduct (fun i => (H i).subtype)))
    (d : ℕ) (hd : 0 < d) :
    Function.Injective (layerMap H w hc d hd) := by
  apply (layerMap H w hc d hd).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro a ha
  have ha' : layerMap H w hc d hd a = 1 := ha
  rw [layerMap_eq_projection H w hc d hd] at ha'
  have hnext := (projection_eq_one_iff H w hc d _).mp ha'
  obtain ⟨b, hb, hlow, hprod⟩ := exists_coords H w hw hc (d + 1) hnext
  let A : ∀ i, H i := fun i => ⟨(a i : G), exactFactor_le H w d i (a i).property⟩
  let B : ∀ i, H i := fun i => ⟨b i, hb i⟩
  have hAB : orderedProduct (fun i => (H i).subtype) A =
      orderedProduct (fun i => (H i).subtype) B := hprod.symm
  have hcoords := hu hAB
  apply Subgroup.mem_bot.mpr
  funext i
  apply Subtype.ext
  change (a i : G) = 1
  by_cases hi : w i = d
  · have hei : (a i : G) = b i :=
      congrArg (fun c : ∀ i, H i => ((c i : H i) : G)) hcoords
    exact hei.trans (hlow i (by omega))
  · exact Subgroup.mem_bot.mp ((exactFactor_of_ne H w hi).le (a i).property)

/-- Every layer class is represented by its exact-height coordinates. -/
theorem layerMap_surjective (hw : ∀ i, 0 < w i) (d : ℕ) (hd : 0 < d) :
    Function.Surjective (layerMap H w hc d hd) := by
  classical
  intro z
  obtain ⟨g, rfl⟩ := projection_surjective H w hc d z
  obtain ⟨c, hcH, hlow, hprod⟩ := exists_coords H w hw hc d g.property
  have hcLevel (i : Fin n) : c i ∈ level H w d := by
    by_cases hi : d ≤ w i
    · exact le_level H w hi (hcH i)
    · rw [hlow i (Nat.lt_of_not_ge hi)]
      exact one_mem _
  let b : Fin n → level H w d := fun i => ⟨c i, hcLevel i⟩
  let a : ∀ i, exactFactor H w d i := fun i =>
    if hi : w i = d then ⟨c i, (exactFactor_of_eq H w hi).symm ▸ hcH i⟩ else 1
  have hprodLevel : (List.ofFn b).prod = g := by
    apply Subtype.ext
    change (level H w d).subtype ((List.ofFn b).prod) = (g : G)
    rw [map_list_prod, List.map_ofFn]
    exact hprod
  have hcoord (i : Fin n) :
      coordinateMap H w hc d i (a i) = projection H w hc d (b i) := by
    by_cases hi : w i = d
    · simp only [a, dite_eq_left hi]
      rfl
    · have ha : a i = 1 := dite_eq_right hi
      rw [ha, map_one]
      symm
      apply (projection_eq_one_iff H w hc d _).mpr
      change c i ∈ level H w (d + 1)
      rcases lt_or_gt_of_ne hi with hi' | hi'
      · rw [hlow i hi']
        exact one_mem _
      · exact le_level H w (by omega) (hcH i)
  refine ⟨a, ?_⟩
  change (List.ofFn fun i => coordinateMap H w hc d i (a i)).prod = _
  simp_rw [hcoord]
  rw [← hprodLevel, map_list_prod, List.map_ofFn]
  rfl

/-- The quotient by the next level is the product of the exact-height factors. -/
def layerEquiv
    (hw : ∀ i, 0 < w i)
    (hu : Function.Injective (orderedProduct (fun i => (H i).subtype)))
    (d : ℕ) (hd : 0 < d) :
    (∀ i, exactFactor H w d i) ≃* Layer H w hc d :=
  MulEquiv.ofBijective (layerMap H w hc d hd)
    ⟨layerMap_injective H w hc hw hu d hd, layerMap_surjective H w hc hw d hd⟩

end Langlands.GroupTheory.HeightLayer
