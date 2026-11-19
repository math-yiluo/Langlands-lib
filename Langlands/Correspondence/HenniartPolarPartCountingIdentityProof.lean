import Langlands.Correspondence.HenniartPolarPart
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The polar-part counting identity

The identity in Lemma 3.3 of the operator's numerical local Langlands route note.
We count the generating coefficient tuples before taking Galois orbits.
-/

noncomputable section

namespace Langlands.Henniart

open Numerical

private abbrev GeneratingTuples (k L : Type*) [Field k] [Field L] [Algebra k L] (J : ℕ) :=
  {c : Fin (J + 1) → L // c 0 ≠ 0 ∧ IntermediateField.adjoin k (Set.range c) = ⊤}

section Support

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable {r d m J : ℕ}

private theorem dvd_polarSupportGcd (c : Fin (m + 1) → L) :
    d ∣ polarSupportGcd c ↔ ∀ i, c i ≠ 0 → d ∣ i.val := by
  classical
  simp only [polarSupportGcd, Finset.dvd_gcd_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    by_cases hz : i.val = 0
    · simp [hz]
    · exact h i ⟨Nat.pos_of_ne_zero hz, hi⟩
  · exact fun h i hi => h i hi.2

open Classical in
private def supportDegree (c : Fin (J + 1) → L) : ℕ :=
  (Finset.univ.filter fun i => c i ≠ 0).sup Fin.val

private theorem le_supportDegree {c : Fin (J + 1) → L} {i : Fin (J + 1)} (hi : c i ≠ 0) :
    i.val ≤ supportDegree c := by
  classical
  unfold supportDegree
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

private theorem supportDegree_mem {c : Fin (J + 1) → L} (h0 : c 0 ≠ 0) :
    ∃ i, i.val = supportDegree c ∧ c i ≠ 0 := by
  classical
  have h : (Finset.univ.filter fun i => c i ≠ 0).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h0⟩⟩
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup _ h Fin.val
  exact ⟨i, he.symm, (Finset.mem_filter.mp hi).2⟩

private def dilatedIndex (h : d * m ≤ J) (i : Fin (m + 1)) : Fin (J + 1) :=
  ⟨d * i.val, Nat.lt_succ_of_le ((Nat.mul_le_mul_left d (Nat.le_of_lt_succ i.isLt)).trans h)⟩

private theorem dilatedIndex_injective (hd : 0 < d) (h : d * m ≤ J) :
    Function.Injective (dilatedIndex h) := fun _ _ he =>
  Fin.ext (Nat.eq_of_mul_eq_mul_left hd (congrArg Fin.val he))

private theorem dilatedIndex_zero (h : d * m ≤ J) : dilatedIndex h 0 = 0 :=
  Fin.ext (Nat.mul_zero d)

/-- Extend a tuple along the index map `i ↦ d * i`, with zeros at the other indices. -/
private def dilateCoefficients (h : d * m ≤ J) (c : Fin (m + 1) → L) : Fin (J + 1) → L :=
  Function.extend (dilatedIndex h) c (fun _ => 0)

private theorem dilateCoefficients_apply (hd : 0 < d) (h : d * m ≤ J)
    (c : Fin (m + 1) → L) (i : Fin (m + 1)) :
    dilateCoefficients h c (dilatedIndex h i) = c i :=
  (dilatedIndex_injective hd h).extend_apply c (fun _ => 0) i

private theorem dilateCoefficients_ne_zero (hd : 0 < d) (h : d * m ≤ J)
    (c : Fin (m + 1) → L) (i : Fin (J + 1)) :
    dilateCoefficients h c i ≠ 0 ↔ ∃ a, dilatedIndex h a = i ∧ c a ≠ 0 := by
  classical
  by_cases hi : ∃ a, dilatedIndex h a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [dilateCoefficients_apply hd]
    exact ⟨fun ha => ⟨a, rfl, ha⟩, fun ⟨b, hb, hc⟩ =>
      (dilatedIndex_injective hd h hb) ▸ hc⟩
  · rw [dilateCoefficients, Function.extend_apply' _ _ _ hi]
    exact ⟨fun hz => (hz rfl).elim, fun ⟨a, ha, _⟩ => (hi ⟨a, ha⟩).elim⟩

private theorem adjoin_dilateCoefficients (hd : 0 < d) (h : d * m ≤ J)
    (c : Fin (m + 1) → L) :
    IntermediateField.adjoin k (Set.range (dilateCoefficients h c)) =
      IntermediateField.adjoin k (Set.range c) := by
  apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff]
  · rintro _ ⟨i, rfl⟩
    by_cases hi : dilateCoefficients h c i = 0
    · rw [hi]
      exact zero_mem _
    · obtain ⟨a, rfl, _⟩ := (dilateCoefficients_ne_zero hd h c i).mp hi
      rw [dilateCoefficients_apply hd]
      exact IntermediateField.subset_adjoin k _ ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact IntermediateField.subset_adjoin k _ ⟨dilatedIndex h a, dilateCoefficients_apply hd h c a⟩

private theorem polarSupportGcd_dilateCoefficients (hd : 0 < d) (h : d * m ≤ J)
    (c : Fin (m + 1) → L) :
    polarSupportGcd (dilateCoefficients h c) = d * polarSupportGcd c := by
  classical
  unfold polarSupportGcd
  have hs : (Finset.univ.filter fun i => 0 < i.val ∧ dilateCoefficients h c i ≠ 0) =
      (Finset.univ.filter fun i => 0 < i.val ∧ c i ≠ 0).image (dilatedIndex h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hi, hc⟩
      obtain ⟨a, rfl, ha⟩ := (dilateCoefficients_ne_zero hd h c i).mp hc
      exact ⟨a, ⟨Nat.pos_of_mul_pos_left hi, ha⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
      exact ⟨Nat.mul_pos hd ha, by rwa [dilateCoefficients_apply hd]⟩
  rw [hs, Finset.gcd_image]
  simpa only [Function.comp_def, dilatedIndex, normalize_eq] using
    (Finset.gcd_mul_left (s := Finset.univ.filter fun i => 0 < i.val ∧ c i ≠ 0)
      (f := Fin.val) (a := d))

private theorem gcd_dilateCoefficients (hd : 0 < d) (hdr : d ∣ r) (h : d * m ≤ J)
    (c : Fin (m + 1) → L) :
    r.gcd (polarSupportGcd (dilateCoefficients h c)) =
      d * (r / d).gcd (polarSupportGcd c) := by
  rw [polarSupportGcd_dilateCoefficients hd, ← Nat.gcd_mul_left, Nat.mul_div_cancel' hdr]

private theorem supportDegree_dilateCoefficients (hd : 0 < d) (h : d * m ≤ J)
    {c : Fin (m + 1) → L} (hm : c (Fin.last m) ≠ 0) :
    supportDegree (dilateCoefficients h c) = d * m := by
  classical
  apply le_antisymm
  · unfold supportDegree
    apply Finset.sup_le
    intro i hi
    obtain ⟨a, rfl, _⟩ :=
      (dilateCoefficients_ne_zero hd h c i).mp (Finset.mem_filter.mp hi).2
    exact Nat.mul_le_mul_left d (Nat.le_of_lt_succ a.isLt)
  · exact le_supportDegree (i := dilatedIndex h (Fin.last m))
      (by rwa [dilateCoefficients_apply hd])

private abbrev PolarTuples (k L : Type*) [Field k] [Field L] [Algebra k L] (r J : ℕ) :=
  Σ d : r.divisors, Σ m : Fin (J / d.val + 1), polarParts k L (r / d.val) m.val

private theorem dilatedIndex_bound (d : r.divisors) (m : Fin (J / d.val + 1)) :
    d.val * m.val ≤ J := by
  rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors d.property)]
  exact Nat.le_of_lt_succ m.isLt

private def assembleTuple (a : PolarTuples k L r J) : GeneratingTuples k L J := by
  obtain ⟨d, m, ⟨c, hc⟩⟩ := a
  have hc' : IsPolarPart k (r / d.val) m.val c := hc
  have hd := Nat.pos_of_mem_divisors d.property
  refine ⟨dilateCoefficients (dilatedIndex_bound d m) c, ?_, ?_⟩
  · rw [← dilatedIndex_zero (dilatedIndex_bound d m), dilateCoefficients_apply hd]
    exact hc'.1
  · rw [adjoin_dilateCoefficients hd]
    exact hc'.2.2.1

private theorem assembleTuple_gcd (a : PolarTuples k L r J) :
    r.gcd (polarSupportGcd (assembleTuple a).val) = a.1.val := by
  obtain ⟨d, m, ⟨c, hc⟩⟩ := a
  have hc' : IsPolarPart k (r / d.val) m.val c := hc
  change r.gcd (polarSupportGcd (dilateCoefficients (dilatedIndex_bound d m) c)) = d.val
  rw [gcd_dilateCoefficients (Nat.pos_of_mem_divisors d.property)
    (Nat.dvd_of_mem_divisors d.property), hc'.2.2.2, mul_one]

private theorem assembleTuple_degree (a : PolarTuples k L r J) :
    supportDegree (assembleTuple a).val = a.1.val * a.2.1.val := by
  obtain ⟨d, m, ⟨c, hc⟩⟩ := a
  have hc' : IsPolarPart k (r / d.val) m.val c := hc
  exact supportDegree_dilateCoefficients (Nat.pos_of_mem_divisors d.property) _ hc'.2.1

private theorem assembleTuple_injective : Function.Injective (assembleTuple (k := k) (L := L)
    (r := r) (J := J)) := by
  rintro ⟨d, m, ⟨c, hc⟩⟩ ⟨e, l, ⟨b, hb⟩⟩ he
  have hde : d = e := Subtype.ext ((assembleTuple_gcd ⟨d, m, c, hc⟩).symm.trans
    ((congrArg (fun a => r.gcd (polarSupportGcd a.val)) he).trans
      (assembleTuple_gcd ⟨e, l, b, hb⟩)))
  subst e
  have hd := Nat.pos_of_mem_divisors d.property
  have hml : m = l := Fin.ext (Nat.eq_of_mul_eq_mul_left hd
    ((assembleTuple_degree ⟨d, m, c, hc⟩).symm.trans
      ((congrArg (fun a => supportDegree a.val) he).trans (assembleTuple_degree ⟨d, l, b, hb⟩))))
  subst l
  have hcb : c = b := by
    funext i
    have hi := congrFun (congrArg Subtype.val he) (dilatedIndex (dilatedIndex_bound d m) i)
    change dilateCoefficients (dilatedIndex_bound d m) c _ =
      dilateCoefficients (dilatedIndex_bound d m) b _ at hi
    simpa only [dilateCoefficients_apply hd] using hi
  subst b
  rfl

private theorem assembleTuple_surjective (hr : 0 < r) :
    Function.Surjective (assembleTuple (k := k) (L := L) (r := r) (J := J)) := by
  rintro ⟨b, hb₀, hbgen⟩
  let g := r.gcd (polarSupportGcd b)
  have hg_dvd : g ∣ r := Nat.gcd_dvd_left _ _
  have hg : 0 < g := Nat.pos_of_dvd_of_pos hg_dvd hr
  have hsupport : ∀ i, b i ≠ 0 → g ∣ i.val :=
    (dvd_polarSupportGcd b).mp (Nat.gcd_dvd_right _ _)
  obtain ⟨a, ha, hba⟩ := supportDegree_mem hb₀
  have hga : g ∣ a.val := hsupport a hba
  let d : r.divisors := ⟨g, Nat.mem_divisors.mpr ⟨hg_dvd, hr.ne'⟩⟩
  let m : Fin (J / d.val + 1) := ⟨a.val / g,
    Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ a.isLt))⟩
  have hdm : d.val * m.val = a.val := Nat.mul_div_cancel' hga
  let h := dilatedIndex_bound d m
  let c : Fin (m.val + 1) → L := b ∘ dilatedIndex h
  have he : dilateCoefficients h c = b := by
    funext i
    by_cases hi : ∃ x, dilatedIndex h x = i
    · obtain ⟨x, rfl⟩ := hi
      exact dilateCoefficients_apply hg h c x
    · rw [dilateCoefficients, Function.extend_apply' _ _ _ hi]
      by_contra hbi
      have hdvi : g ∣ i.val := hsupport i (Ne.symm hbi)
      have hib : i.val ≤ a.val := ha ▸ le_supportDegree (Ne.symm hbi)
      let x : Fin (m.val + 1) := ⟨i.val / g,
        Nat.lt_succ_of_le (Nat.div_le_div_right hib)⟩
      exact hi ⟨x, Fin.ext (Nat.mul_div_cancel' hdvi)⟩
  have hc : IsPolarPart k (r / d.val) m.val c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change b (dilatedIndex h 0) ≠ 0
      rwa [dilatedIndex_zero]
    · have hlast : dilatedIndex h (Fin.last m.val) = a := Fin.ext hdm
      change b (dilatedIndex h (Fin.last m.val)) ≠ 0
      rwa [hlast]
    · rw [← adjoin_dilateCoefficients hg h, he]
      exact hbgen
    · have hscaled := gcd_dilateCoefficients hg hg_dvd h c
      rw [he] at hscaled
      exact Nat.eq_of_mul_eq_mul_left hg (hscaled.symm.trans (Nat.mul_one g).symm)
  exact ⟨⟨d, m, c, hc⟩, Subtype.ext he⟩

private theorem card_generatingTuples_eq_sum [Finite L] (hr : 0 < r) :
    Nat.card (GeneratingTuples k L J) =
      ∑ d ∈ r.divisors, ∑ m ∈ Finset.range (J / d + 1),
        Nat.card (polarParts k L (r / d) m) := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective _
    ⟨assembleTuple_injective (k := k) (L := L) (r := r) (J := J), assembleTuple_surjective hr⟩)]
  unfold PolarTuples
  rw [Nat.card_sigma, ← Finset.sum_coe_sort r.divisors
    (fun d => ∑ m ∈ Finset.range (J / d + 1), Nat.card (polarParts k L (r / d) m))]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.card_sigma]
  exact Fin.sum_univ_eq_sum_range (fun m => Nat.card (polarParts k L (r / d.val) m))
    (J / d.val + 1)

end Support

section Orbits

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

private theorem polar_stabilizer_eq_bot {r m : ℕ} (c : polarParts k L r m) :
    MulAction.stabilizer Gal(L/k) c = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix : g • c = c := hg
  have hc : IsPolarPart k r m c.val := c.property
  let E := IntermediateField.adjoin k (Set.range c.val)
  have hhom : g.toAlgHom.comp E.val = E.val := by
    apply IntermediateField.adjoin_algHom_ext
    rintro _ ⟨i, rfl⟩
    exact congrFun (congrArg Subtype.val hfix) i
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ E := by
    change x ∈ IntermediateField.adjoin k (Set.range c.val)
    rw [hc.2.2.1]
    trivial
  exact DFunLike.congr_fun hhom ⟨x, hx⟩

private theorem card_polarParts (k L : Type*) [Field k] [Field L] [Algebra k L] (r m : ℕ) :
    Nat.card (polarParts k L r m) = Nat.card Gal(L/k) * polarPartCountOf k L r m := by
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd
    (G := Gal(L/k)) (polar_stabilizer_eq_bot (k := k) (L := L) (r := r) (m := m))),
    Nat.card_prod, mul_comm]
  rfl

end Orbits

section Subfields

variable {k L : Type*} [Field k] [Field L] [Algebra k L] {J : ℕ}

private abbrev NonzeroConstantTuples (L : Type*) [Field L] (J : ℕ) :=
  {c : Fin (J + 1) → L // c 0 ≠ 0}

private theorem card_nonzeroConstantTuples :
    Nat.card (NonzeroConstantTuples L J) = (Nat.card L - 1) * Nat.card L ^ J := by
  let e : (L × (Fin J → L)) ≃ (Fin (J + 1) → L) := Fin.consEquiv (fun _ => L)
  let split : NonzeroConstantTuples L J ≃ {x : L // x ≠ 0} × (Fin J → L) :=
    (Equiv.subtypeEquiv (p := fun u => u.1 ≠ 0) (q := fun c => c 0 ≠ 0) e
      (by
        intro u
        simp [e])).symm.trans
          (Equiv.prodSubtypeFstEquivSubtypeProd (α := L) (β := Fin J → L)
            (p := fun x => x ≠ 0))
  rw [Nat.card_congr split, Nat.card_prod, ← Nat.card_congr unitsEquivNeZero, Nat.card_units,
    Nat.card_fun, Nat.card_fin]

private theorem adjoin_range_comp {ι : Type*} {M : Type*} [Field M] [Algebra k M]
    (e : L →ₐ[k] M) (c : ι → L) :
    IntermediateField.adjoin k (Set.range (e ∘ c)) =
      (IntermediateField.adjoin k (Set.range c)).map e := by
  rw [Set.range_comp, IntermediateField.adjoin_map]

private theorem card_generatingTuples_congr {M : Type*} [Field M] [Algebra k M]
    (e : L ≃ₐ[k] M) :
    Nat.card (GeneratingTuples k L J) = Nat.card (GeneratingTuples k M J) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => e.toEquiv) fun c => ?_
  change c 0 ≠ 0 ∧ IntermediateField.adjoin k (Set.range c) = ⊤ ↔
    e (c 0) ≠ 0 ∧ IntermediateField.adjoin k (Set.range (e.toAlgHom ∘ c)) = ⊤
  rw [map_ne_zero, adjoin_range_comp, ← e.fieldRange_eq_top, AlgHom.fieldRange_eq_map,
    (IntermediateField.map_injective e.toAlgHom).eq_iff]

private theorem card_nonzeroConstantTuples_eq_subfields :
    Nat.card (NonzeroConstantTuples L J) =
      Nat.card (Σ S : IntermediateField k L, GeneratingTuples k S J) := by
  let toTuple : (Σ S : IntermediateField k L, GeneratingTuples k S J) →
      NonzeroConstantTuples L J := fun ⟨S, c⟩ =>
    ⟨S.val ∘ c.val, (map_ne_zero S.val).mpr c.property.1⟩
  have hfield (S : IntermediateField k L) (c : GeneratingTuples k S J) :
      IntermediateField.adjoin k (Set.range (toTuple ⟨S, c⟩).val) = S := by
    change IntermediateField.adjoin k (Set.range (S.val ∘ c.val)) = S
    rw [adjoin_range_comp, c.property.2, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective toTuple ⟨?_, ?_⟩
  · rintro ⟨S, c⟩ ⟨T, b⟩ he
    have hST : S = T := (hfield S c).symm.trans (he ▸ hfield T b)
    subst T
    have hcb : c = b := Subtype.ext
      (funext fun i => S.val.injective (congrFun (congrArg Subtype.val he) i))
    subst b
    rfl
  · rintro ⟨b, h0⟩
    let S := IntermediateField.adjoin k (Set.range b)
    let c : Fin (J + 1) → S := fun i =>
      ⟨b i, IntermediateField.subset_adjoin k (Set.range b) ⟨i, rfl⟩⟩
    have hcomp : S.val ∘ c = b := rfl
    have hgen : IntermediateField.adjoin k (Set.range c) = ⊤ := by
      apply IntermediateField.map_injective S.val
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val, ← adjoin_range_comp, hcomp]
    refine ⟨⟨S, c, ?_, hgen⟩, Subtype.ext hcomp⟩
    exact fun h => h0 (congrArg S.val h)

variable (k L) [Finite k] [Finite L] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Index intermediate fields of a finite-field extension by their degrees. -/
private def subfieldDegreeEquiv : IntermediateField k L ≃ (Module.finrank k L).divisors := by
  letI : Module.Finite k L := Module.Finite.of_finite
  let degree (S : IntermediateField k L) : (Module.finrank k L).divisors :=
    ⟨Module.finrank k S, Nat.mem_divisors.mpr
      ⟨Module.finrank_dvd_finrank_right k S L, Module.finrank_pos.ne'⟩⟩
  refine Equiv.ofBijective degree ⟨?_, ?_⟩
  · intro S T he
    have hdeg : Module.finrank k S = Module.finrank k T := congrArg Subtype.val he
    obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := k) (K := S) (L := T)
      (by rw [hdeg])
    have himage : (T.val.comp e).fieldRange = S := AlgHom.fieldRange_of_normal (T.val.comp e)
    apply IntermediateField.eq_of_le_of_finrank_eq _ hdeg
    rw [← himage]
    intro x hx
    obtain ⟨s, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact (e s).property
  · intro d
    let : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
    obtain ⟨e : FiniteField.Extension k p d.val →ₐ[k] L⟩ :=
      FiniteField.nonempty_algHom_of_finrank_dvd
        ((FiniteField.finrank_extension k p d.val).symm ▸ Nat.dvd_of_mem_divisors d.property)
    exact ⟨e.fieldRange, Subtype.ext
      (e.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans
        (FiniteField.finrank_extension k p d.val))⟩

omit [Finite L] in
private def generatingTupleCount (J d : ℕ) : ℕ :=
  if hd : d ≠ 0 then
    letI : NeZero d := ⟨hd⟩
    Nat.card (GeneratingTuples k (FiniteField.Extension k p d) J)
  else 0

private theorem card_nonzeroConstantTuples_eq_divisor_sum :
    Nat.card (NonzeroConstantTuples L J) =
      ∑ d ∈ (Module.finrank k L).divisors, generatingTupleCount k p J d := by
  classical
  let e := subfieldDegreeEquiv k L p
  rw [card_nonzeroConstantTuples_eq_subfields (k := k),
    Nat.card_congr (Equiv.sigmaCongrLeft' e), Nat.card_sigma,
    ← Finset.sum_coe_sort (Module.finrank k L).divisors (generatingTupleCount k p J)]
  apply Finset.sum_congr rfl
  intro d _
  have hd := (Nat.pos_of_mem_divisors d.property).ne'
  let : NeZero d.val := ⟨hd⟩
  rw [generatingTupleCount, dite_eq_left hd]
  exact card_generatingTuples_congr (FiniteField.algEquivExtension k p d.val (e.symm d)
    (congrArg Subtype.val (e.apply_symm_apply d)))

omit [Finite L] in
private theorem card_generatingTuples_eq_moebius (t : ℕ) [NeZero t] :
    (Nat.card (GeneratingTuples k (FiniteField.Extension k p t) J) : ℤ) =
      ∑ i ∈ t.divisors, ArithmeticFunction.moebius (t / i) * ((Nat.card k : ℤ) ^ i - 1) *
        (Nat.card k : ℤ) ^ (i * J) := by
  have hsum (n : ℕ) (hn : 0 < n) :
      ∑ i ∈ n.divisors, (generatingTupleCount k p J i : ℤ) =
        ((Nat.card k : ℤ) ^ n - 1) * (Nat.card k : ℤ) ^ (n * J) := by
    let : NeZero n := ⟨hn.ne'⟩
    have h := card_nonzeroConstantTuples_eq_divisor_sum (J := J) k
      (FiniteField.Extension k p n) p
    rw [card_nonzeroConstantTuples, FiniteField.finrank_extension, FiniteField.natCard_extension] at h
    have hpos : 1 ≤ Nat.card k ^ n := pow_pos Nat.card_pos n
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Int.ofNat_sub hpos, Nat.cast_one,
      ← pow_mul] using (congrArg (fun x : ℕ => (x : ℤ)) h).symm
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum t (NeZero.pos t)
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
    ArithmeticFunction.moebius a * (((Nat.card k : ℤ) ^ b - 1) * (Nat.card k : ℤ) ^ (b * J)))] at h
  simpa only [generatingTupleCount, dite_eq_left (NeZero.ne t), mul_assoc] using h.symm

end Subfields

private theorem sum_polarPartCountOf_eq_sum (q n f j : ℕ) [Fact q.minFac.Prime] [NeZero f]
    (hq : IsPrimePow q) (hn : 1 ≤ n) (hfn : f ∣ n) {d : ℕ} (hd : d ∈ (n / f).divisors) :
    (∑ m ∈ Finset.range (j / f / d + 1),
      polarPartCountOf (polarBaseField q) (polarExtensionField q f) (n / f / d) m) =
      ∑ s ∈ (Finset.range (j + 1)).filter (fun s => f ∣ s ∧ d * s ≤ j),
        polarPartCount q (n / d) f s := by
  have hf := NeZero.pos f
  have hdpos := Nat.pos_of_mem_divisors hd
  have hfdn := (Nat.dvd_div_iff_mul_dvd hfn).mp (Nat.dvd_of_mem_divisors hd)
  have hdn : d ∣ n := (dvd_mul_left d f).trans hfdn
  have hfd : f ∣ n / d := (Nat.dvd_div_iff_mul_dvd hdn).mpr (by simpa [mul_comm] using hfdn)
  have hnd : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
  have hbound (m : ℕ) : m ∈ Finset.range (j / f / d + 1) ↔ d * (f * m) ≤ j := by
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hdpos, Nat.le_div_iff_mul_le hf]
    rw [show (m * d) * f = d * (f * m) by ac_rfl]
  refine Finset.sum_bij (fun m _ => f * m) ?_ ?_ ?_ ?_
  · intro m hm
    have hmj := (hbound m).mp hm
    have hle := (Nat.le_mul_of_pos_left (f * m) hdpos).trans hmj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), dvd_mul_right f m, hmj⟩
  · intro m _ l _ he
    exact Nat.eq_of_mul_eq_mul_left hf he
  · intro s hs
    obtain ⟨_, ⟨m, rfl⟩, hsj⟩ := Finset.mem_filter.mp hs
    exact ⟨m, (hbound m).mpr hsj, rfl⟩
  · intro m _
    rw [polarPartCount, dite_eq_left ⟨hq, hnd, hf, hfd, dvd_mul_right f m⟩,
      Nat.mul_div_cancel_left _ hf, Nat.div_right_comm n f d]

/-- The polar-part counting identity of route-note Lemma 3.3. -/
theorem polarPartCountingIdentity : PolarPartCountingIdentityStatement := by
  intro q hq n f j hn hf hfn
  let : Fact q.minFac.Prime := ⟨Nat.minFac_prime hq.ne_one⟩
  let : NeZero f := ⟨ne_of_gt (show 0 < f from hf)⟩
  have hqcard : Nat.card (polarBaseField q) = q :=
    (GaloisField.card q.minFac (q.factorization q.minFac)
      (Nat.factorization_minFac_ne_zero hq.one_lt)).trans
      hq.minFac_pow_factorization_eq
  have hr : 0 < n / f := Nat.div_pos (Nat.le_of_dvd hn hfn) hf
  have hcount : Nat.card (GeneratingTuples (polarBaseField q) (polarExtensionField q f) (j / f)) =
      f * ∑ d ∈ (n / f).divisors,
        ∑ s ∈ (Finset.range (j + 1)).filter (fun s => f ∣ s ∧ d * s ≤ j),
          polarPartCount q (n / d) f s := by
    rw [card_generatingTuples_eq_sum hr]
    simp_rw [card_polarParts, FiniteField.natCard_algEquiv_extension, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun d hd => sum_polarPartCountOf_eq_sum q n f j hq hn hfn hd)
  have hcast := congrArg (fun a : ℕ => (a : ℤ)) hcount
  simp only [Nat.cast_mul, Nat.cast_sum] at hcast
  rw [← hcast, card_generatingTuples_eq_moebius (polarBaseField q) q.minFac f, hqcard]

end Langlands.Henniart
