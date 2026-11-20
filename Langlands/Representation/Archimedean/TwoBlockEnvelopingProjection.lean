import Langlands.Representation.Archimedean.TwoBlockEnvelopingPBW
import Langlands.Representation.Archimedean.LowerVermaCentral

/-! # Parabolic projection of the complex matrix center -/

noncomputable section

open scoped Classical
set_option autoImplicit false

namespace Langlands.Archimedean.TwoBlockEnveloping

open VermaPBW Kostant
open Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n a : ℕ)

local notation "U" => VermaGL.glU n
local notation "UL" => UniversalEnvelopingAlgebra ℂ (blockLevi n a)

theorem blockLetterWeight_eq_one_iff (i j : Fin n) :
    blockLetterWeight n a (i, j) = 1 ↔ i.val < a ∧ a ≤ j.val := by
  unfold blockLetterWeight blockDiagonalGrade
  by_cases hi : i.val < a <;> by_cases hj : j.val < a <;>
    norm_num [hi, hj, ← Nat.not_lt]

theorem blockLetterWeight_eq_neg_one_iff (i j : Fin n) :
    blockLetterWeight n a (i, j) = -1 ↔ a ≤ i.val ∧ j.val < a := by
  unfold blockLetterWeight blockDiagonalGrade
  by_cases hi : i.val < a <;> by_cases hj : j.val < a <;>
    norm_num [hi, hj, ← Nat.not_lt]

private theorem unit_mem_upperSpan (c : Idx n) (hc : blockLetterWeight n a c = 1) (u : U) :
    UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * u ∈ upperRadicalRightSpan n a :=
  Submodule.subset_span ⟨(⟨c, hc⟩, u), rfl⟩

/-- The upper radical span is closed under right multiplication in the ambient algebra. -/
theorem upperRadicalRightSpan_mul {x : U} (hx : x ∈ upperRadicalRightSpan n a) (y : U) :
    x * y ∈ upperRadicalRightSpan n a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, v⟩, rfl⟩ := hx
    rw [mul_assoc]
    exact unit_mem_upperSpan n a c.val c.property (v * y)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul k x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ k hx

private theorem units_commute_of_upper (c d : Idx n)
    (hc : blockLetterWeight n a c = 1) (hd : blockLetterWeight n a d = 1) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ (unitE n c))
      (UniversalEnvelopingAlgebra.ι ℂ (unitE n d)) := by
  obtain ⟨hc₁, hc₂⟩ := (blockLetterWeight_eq_one_iff n a c.1 c.2).mp hc
  obtain ⟨hd₁, hd₂⟩ := (blockLetterWeight_eq_one_iff n a d.1 d.2).mp hd
  apply sub_eq_zero.mp
  change VermaGL.unitU n c.1 c.2 * VermaGL.unitU n d.1 d.2 -
    VermaGL.unitU n d.1 d.2 * VermaGL.unitU n c.1 c.2 = 0
  rw [VermaCentral.unitU_comm]
  have hcd : c.2 ≠ d.1 := fun h => hc₂.not_gt (h.symm ▸ hd₁)
  have hdc : d.2 ≠ c.1 := fun h => hd₂.not_gt (h.symm ▸ hc₁)
  simp [hcd, hdc]

private theorem W_replicate (c : Idx n) (k : ℕ) :
    W n (List.replicate k c) = UniversalEnvelopingAlgebra.ι ℂ (unitE n c) ^ k := by
  induction k with
  | zero => simp [W_nil]
  | succ k ih => rw [List.replicate_succ, W_cons, ih, pow_succ']

private theorem upper_word_insert (c : Idx n) (hc : blockLetterWeight n a c = 1)
    (α : Idx n →₀ ℕ) (l : List (Idx n)) (hnd : l.Nodup) (hc' : c ∈ l)
    (hl : ∀ d ∈ l, blockLetterWeight n a d = 1) :
    UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * W n (expand l α) =
      W n (expand l (α + Finsupp.single c 1)) := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil hc')
  | cons d l ih =>
    have hnd' := List.nodup_cons.mp hnd
    have splitWord (β : Idx n →₀ ℕ) :
        W n (expand (d :: l) β) =
          UniversalEnvelopingAlgebra.ι ℂ (unitE n d) ^ (β d) * W n (expand l β) := by
      rw [show expand (d :: l) β = List.replicate (β d) d ++ expand l β from rfl,
        W_append, W_replicate]
    rw [splitWord, splitWord, Finsupp.add_apply]
    by_cases h : d = c
    · subst d
      rw [Finsupp.single_eq_same, pow_succ']
      have he : expand l (α + Finsupp.single c 1) = expand l α :=
        expand_congr fun x hx => by
          have hxc : c ≠ x := fun h => hnd'.1 (h.symm ▸ hx)
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hxc.symm, add_zero]
      rw [he, mul_assoc]
    · rw [Finsupp.single_eq_of_ne h, add_zero, ← mul_assoc,
        ((units_commute_of_upper n a c d hc (hl d List.mem_cons_self)).pow_right (α d)).eq,
        mul_assoc]
      apply congrArg (_ * ·)
      exact ih hnd'.2 ((List.mem_cons.mp hc').resolve_left (Ne.symm h))
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))

private theorem unit_mul_blockPBWBasis (c : Idx n) (hc : blockLetterWeight n a c = 1)
    (α : Idx n →₀ ℕ) :
    UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * blockPBWBasis n a α =
      blockPBWBasis n a (α + Finsupp.single c 1) := by
  have splitBlock (β : Idx n →₀ ℕ) :
      blockPBWBasis n a β = W n (expand (weightLetters n a 1) β) *
        W n (expand (weightLetters n a 0 ++ weightLetters n a (-1)) β) := by
    rw [blockPBWBasis_apply, blockLetters, expand_append, W_append]
  rw [splitBlock α, splitBlock (α + Finsupp.single c 1), ← mul_assoc]
  have hnd : (weightLetters n a 1).Nodup :=
    (Finset.nodup_toList (Finset.univ : Finset {c : Idx n // blockLetterWeight n a c = 1})).map
      Subtype.val_injective
  rw [upper_word_insert n a c hc α _ hnd ((mem_weightLetters n a 1 c).mpr hc)
    (fun d hd => (mem_weightLetters n a 1 d).mp hd)]
  congr 2
  refine expand_congr fun d hd => ?_
  have hnc : c ≠ d := by
    rintro rfl
    rcases List.mem_append.mp hd with hd | hd
    · have h := hc.symm.trans ((mem_weightLetters n a 0 c).mp hd)
      norm_num at h
    · have h := hc.symm.trans ((mem_weightLetters n a (-1) c).mp hd)
      norm_num at h
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hnc.symm, add_zero]

private abbrev LeviIdx := {c : Idx n // blockLetterWeight n a c = 0}

private def leviLetters : List (LeviIdx n a) := Finset.univ.toList

private theorem levi_trans (i j k : Fin n) :
    blockLetterWeight n a (i, j) = 0 → blockLetterWeight n a (j, k) = 0 →
      blockLetterWeight n a (i, k) = 0 := by
  simp only [blockLetterWeight, sub_eq_zero]
  exact Eq.trans

private def leviMonomial (β : LeviIdx n a →₀ ℕ) : UL :=
  orderedMonomial ℂ (blockLevi n a)
    (subBasis n (fun i j => blockLetterWeight n a (i, j) = 0) (levi_trans n a))
    (leviLetters n a) β

private theorem leviMonomial_span : ⊤ ≤ Submodule.span ℂ (Set.range (leviMonomial n a)) :=
  top_le_span_subMonomial n _ (levi_trans n a) _ (Finset.nodup_toList _)
    (fun c => Finset.mem_toList.mpr (Finset.mem_univ c))

private def LeviSupported (α : Idx n →₀ ℕ) : Prop :=
  ∀ c, blockLetterWeight n a c ≠ 0 → α c = 0

private theorem leviInclusion_leviMonomial (β : LeviIdx n a →₀ ℕ) :
    leviInclusion n a (leviMonomial n a β) =
      blockPBWBasis n a (β.embDomain (Function.Embedding.subtype _)) := by
  rw [blockPBWBasis_apply, blockLetters, expand_append, expand_append]
  have hs (c : Idx n) (hc : blockLetterWeight n a c ≠ 0) :
      (β.embDomain (Function.Embedding.subtype _)) c = 0 :=
    Finsupp.embDomain_of_notMem_range _ _ _ (by rintro ⟨d, rfl⟩; exact hc d.property)
  have he (k : ℂ) (hk : k ≠ 0) :
      expand (weightLetters n a k) (β.embDomain (Function.Embedding.subtype _)) = [] := by
    rw [← expand_zero (weightLetters n a k)]
    exact expand_congr fun c hc => hs c (((mem_weightLetters n a k c).mp hc) ▸ hk)
  rw [he 1 one_ne_zero, he (-1) (neg_ne_zero.mpr one_ne_zero), List.nil_append, List.append_nil]
  change subInc n _ (levi_trans n a)
    (word ℂ (subalg n _ (levi_trans n a))
      ((expand (leviLetters n a) β).map (subBasis n _ (levi_trans n a)))) = _
  rw [subInc_word]
  congr 1
  exact (expand_map Subtype.val (leviLetters n a) _ β
    (fun c _ => Finsupp.embDomain_apply_self (Function.Embedding.subtype _) β c)).symm

/-- The linear PBW projection that keeps the monomials supported on the Levi. -/
def blockLeviLinearProjection : U →ₗ[ℂ] UL :=
  (blockPBWBasis n a).constr ℂ fun α =>
    if LeviSupported n a α then
      leviMonomial n a (α.subtypeDomain fun c => blockLetterWeight n a c = 0)
    else 0

theorem blockLeviLinearProjection_leviInclusion (x : UL) :
    blockLeviLinearProjection n a (leviInclusion n a x) = x := by
  have hx := leviMonomial_span n a (show x ∈ (⊤ : Submodule ℂ UL) from trivial)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, rfl⟩ := hx
    rw [leviInclusion_leviMonomial, blockLeviLinearProjection, Module.Basis.constr_basis,
      ite_eq_left]
    · congr 1
      ext c
      exact Finsupp.embDomain_apply_self (Function.Embedding.subtype _) β c
    · intro c hc
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨d, rfl⟩
      exact hc d.property
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

theorem leviInclusion_injective : Function.Injective (leviInclusion n a) :=
  Function.LeftInverse.injective (blockLeviLinearProjection_leviInclusion n a)

theorem blockLeviLinearProjection_eq_zero_of_mem_upperSpan {x : U}
    (hx : x ∈ upperRadicalRightSpan n a) : blockLeviLinearProjection n a x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, v⟩, rfl⟩ := hx
    let f := (blockLeviLinearProjection n a).comp
      (LinearMap.mulLeft ℂ (UniversalEnvelopingAlgebra.ι ℂ (unitE n c.val)))
    have hf : f = 0 := by
      apply (blockPBWBasis n a).ext
      intro α
      change blockLeviLinearProjection n a
        (UniversalEnvelopingAlgebra.ι ℂ (unitE n c.val) * blockPBWBasis n a α) = 0
      rw [unit_mul_blockPBWBasis n a _ c.property, blockLeviLinearProjection,
        Module.Basis.constr_basis, ite_eq_right]
      intro hs
      have he := hs c.val (by rw [c.property]; exact one_ne_zero)
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at he
      omega
    exact LinearMap.congr_fun hf v
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- On the grading centralizer, the projection agrees with the original element
modulo the upper radical span. -/
theorem sub_leviInclusion_projection_mem_upperSpan (z : U)
    (hz : Commute (blockGradeElement n a) z) :
    z - leviInclusion n a (blockLeviLinearProjection n a z) ∈ upperRadicalRightSpan n a := by
  have h := mem_levi_sup_upperRadicalRightSpan_of_commute n a z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨l, hl⟩ := hx
  have e : leviInclusion n a l = x := hl
  rw [← e, map_add, blockLeviLinearProjection_leviInclusion,
    blockLeviLinearProjection_eq_zero_of_mem_upperSpan n a hy, add_zero, add_sub_cancel_left]
  exact hy

private theorem levi_unit_commutator_mem_upperSpan (c d : Idx n)
    (hc : blockLetterWeight n a c = 0) (hd : blockLetterWeight n a d = 1) :
    VermaGL.unitU n c.1 c.2 * VermaGL.unitU n d.1 d.2 -
      VermaGL.unitU n d.1 d.2 * VermaGL.unitU n c.1 c.2 ∈ upperRadicalRightSpan n a := by
  rw [VermaCentral.unitU_comm]
  apply Submodule.sub_mem
  · split_ifs with h
    · have hw : blockLetterWeight n a (c.1, d.2) = 1 := by
        unfold blockLetterWeight at hc hd ⊢
        rw [← h] at hd
        linear_combination hc + hd
      simpa only [mul_one, unitE] using unit_mem_upperSpan n a (c.1, d.2) hw 1
    · exact Submodule.zero_mem _
  · split_ifs with h
    · have hw : blockLetterWeight n a (d.1, c.2) = 1 := by
        unfold blockLetterWeight at hc hd ⊢
        rw [h] at hd
        linear_combination hd + hc
      simpa only [mul_one, unitE] using unit_mem_upperSpan n a (d.1, c.2) hw 1
    · exact Submodule.zero_mem _

private theorem levi_unit_mul_mem_upperSpan (c : Idx n) (hc : blockLetterWeight n a c = 0)
    {u : U} (hu : u ∈ upperRadicalRightSpan n a) :
    VermaGL.unitU n c.1 c.2 * u ∈ upperRadicalRightSpan n a := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨⟨d, v⟩, rfl⟩ := hu
    let x := VermaGL.unitU n c.1 c.2
    let y := VermaGL.unitU n d.val.1 d.val.2
    change x * (y * v) ∈ upperRadicalRightSpan n a
    rw [show x * (y * v) = (x * y - y * x) * v + y * (x * v) by noncomm_ring]
    exact Submodule.add_mem _ (upperRadicalRightSpan_mul n a
      (levi_unit_commutator_mem_upperSpan n a c d.val hc d.property) v)
      (unit_mem_upperSpan n a d.val d.property (x * v))
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ k hx

theorem leviInclusion_ι (X : blockLevi n a) :
    leviInclusion n a (UniversalEnvelopingAlgebra.ι ℂ X) =
      UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ) := by
  unfold blockLevi at X
  exact subInc_ι n _ (levi_trans n a) X

private theorem levi_generator_mul_mem_upperSpan (X : blockLevi n a)
    {u : U} (hu : u ∈ upperRadicalRightSpan n a) :
    leviInclusion n a (UniversalEnvelopingAlgebra.ι ℂ X) * u ∈ upperRadicalRightSpan n a := by
  let B : Module.Basis (LeviIdx n a) ℂ (blockLevi n a) :=
    subBasis n (fun i j => blockLetterWeight n a (i, j) = 0) (levi_trans n a)
  have h : ∑ c, B.repr X c • B c = X := B.sum_repr X
  rw [leviInclusion_ι, ← h]
  change (UniversalEnvelopingAlgebra.ι ℂ)
    ((blockLevi n a).incl (∑ c, B.repr X c • B c)) * u ∈ _
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [map_smul, map_smul, smul_mul_assoc]
  change (B.repr X c) • ((UniversalEnvelopingAlgebra.ι ℂ)
    (↑(subBasis n _ (levi_trans n a) c) : Matrix (Fin n) (Fin n) ℂ) * u) ∈ _
  rw [coe_subBasis]
  exact Submodule.smul_mem _ _ (levi_unit_mul_mem_upperSpan n a c.val c.property hu)

/-- The upper radical span is stable under left multiplication by Levi operators. -/
theorem leviInclusion_mul_mem_upperSpan (l : UL) {u : U} (hu : u ∈ upperRadicalRightSpan n a) :
    leviInclusion n a l * u ∈ upperRadicalRightSpan n a := by
  let A := (leviInclusion n a).comp (UniversalEnvelopingAlgebra.mkAlgHom ℂ (blockLevi n a))
  suffices h : ∀ t : TensorAlgebra ℂ (blockLevi n a), ∀ v : U,
      v ∈ upperRadicalRightSpan n a → A t * v ∈ upperRadicalRightSpan n a from
    Quotient.inductionOn l (fun t => h t u hu)
  intro t
  induction t using TensorAlgebra.induction with
  | algebraMap k =>
    intro u hu
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ hu
  | ι X => exact fun _ hu => levi_generator_mul_mem_upperSpan n a X hu
  | mul t s ht hs =>
    intro u hu
    rw [map_mul, mul_assoc]
    exact ht _ (hs _ hu)
  | add t s ht hs =>
    intro u hu
    rw [map_add, add_mul]
    exact Submodule.add_mem _ (ht _ hu) (hs _ hu)

private theorem center_sub_projection_mem_upperSpan (z : VermaGL.center n) :
    (z : U) - leviInclusion n a (blockLeviLinearProjection n a z) ∈ upperRadicalRightSpan n a :=
  sub_leviInclusion_projection_mem_upperSpan n a z
    (Subalgebra.mem_center_iff.mp z.property (blockGradeElement n a))

private theorem blockLeviLinearProjection_mem_center (z : VermaGL.center n) :
    blockLeviLinearProjection n a z ∈ Subalgebra.center ℂ UL := by
  refine Subalgebra.mem_center_iff.mpr fun l => sub_eq_zero.mp ?_
  let p := blockLeviLinearProjection n a (z : U)
  let r := (z : U) - leviInclusion n a p
  have hr : r ∈ upperRadicalRightSpan n a := center_sub_projection_mem_upperSpan n a z
  have hz := Subalgebra.mem_center_iff.mp z.property (leviInclusion n a l)
  change l * p - p * l = 0
  have h : leviInclusion n a (l * p - p * l) =
      r * leviInclusion n a l - leviInclusion n a l * r := by
    have hp : leviInclusion n a p = (z : U) - r := (sub_sub_cancel _ _).symm
    rw [map_sub, map_mul, map_mul, hp, mul_sub, sub_mul, hz]
    abel
  rw [← blockLeviLinearProjection_leviInclusion n a (l * p - p * l), h]
  exact blockLeviLinearProjection_eq_zero_of_mem_upperSpan n a
    (Submodule.sub_mem _ (upperRadicalRightSpan_mul n a hr _)
      (leviInclusion_mul_mem_upperSpan n a l hr))

/-- The parabolic center homomorphism for the two-block Levi subalgebra. -/
def blockLeviCenterProjection : VermaGL.center n →ₐ[ℂ] Subalgebra.center ℂ UL where
  toFun z := ⟨blockLeviLinearProjection n a z, blockLeviLinearProjection_mem_center n a z⟩
  map_one' := by
    apply Subtype.ext
    change blockLeviLinearProjection n a 1 = 1
    simpa only [map_one] using blockLeviLinearProjection_leviInclusion n a (1 : UL)
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_mul' z w := by
    apply Subtype.ext
    let p := blockLeviLinearProjection n a (z : U)
    let q := blockLeviLinearProjection n a (w : U)
    let i := leviInclusion n a
    change blockLeviLinearProjection n a ((z : U) * (w : U)) = p * q
    have h : (z : U) * (w : U) - i (p * q) =
        ((w : U) - i q) * (z : U) + ((z : U) - i p) * i q := by
      have hz := Subalgebra.mem_center_iff.mp z.property
      rw [map_mul, sub_mul, sub_mul, hz (w : U), hz (i q)]
      abel
    have hz : (z : U) * (w : U) - i (p * q) ∈ upperRadicalRightSpan n a := by
      rw [h]
      exact Submodule.add_mem _
        (upperRadicalRightSpan_mul n a (center_sub_projection_mem_upperSpan n a w) _)
        (upperRadicalRightSpan_mul n a (center_sub_projection_mem_upperSpan n a z) _)
    have he := blockLeviLinearProjection_eq_zero_of_mem_upperSpan n a hz
    rw [map_sub, blockLeviLinearProjection_leviInclusion, sub_eq_zero] at he
    exact he
  commutes' k := by
    apply Subtype.ext
    change blockLeviLinearProjection n a (algebraMap ℂ U k) = algebraMap ℂ UL k
    rw [← (leviInclusion n a).commutes k, blockLeviLinearProjection_leviInclusion]

theorem sub_leviInclusion_centerProjection_mem_upperSpan (z : VermaGL.center n) :
    (z : U) - leviInclusion n a (blockLeviCenterProjection n a z) ∈ upperRadicalRightSpan n a :=
  center_sub_projection_mem_upperSpan n a z

/-- The ordinary Harish-Chandra polynomial functional vanishes on the upper radical span. -/
theorem gam_eq_zero_of_mem_upperRadicalRightSpan {v : U}
    (hv : v ∈ upperRadicalRightSpan n a) : VermaCentral.gam n v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨c, u⟩, rfl⟩ := hv
    obtain ⟨hi, hj⟩ := (blockLetterWeight_eq_one_iff n a _ _).mp c.property
    have hc : c.val.1 < c.val.2 :=
      show c.val.1.val < c.val.2.val from lt_of_lt_of_le hi hj
    refine MvPolynomial.funext fun lam => ?_
    rw [map_zero, VermaCentral.eval_gam, Psi_unitE_up_mul n lam 0 ⟨c.val, hc⟩]
    simp [vVal, hc, supCoeff]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Langlands.Archimedean.TwoBlockEnveloping
