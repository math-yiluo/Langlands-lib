import Langlands.LinearAlgebra.RootDatumIsogenyBaseStatement
import Langlands.GroupScheme.SplitExistence.IntegralBase

/-! # Isogenies of reduced root data carry bases to bases -/

noncomputable section

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace Langlands.LinearAlgebra

namespace RootDatumIsogenyBaseProof

open RootPairing Set IsAddIndecomposable

section OneDatum

variable {J : Type u₁} {X : Type u₂} {Y : Type u₃}
    [Finite J] [AddCommGroup X] [AddCommGroup Y]
    {P : RootDatum J X Y} [P.IsReduced]

omit [P.IsReduced] in
private theorem functional_pos_of_isPos (b : P.Base) (l : X →ₗ[ℤ] ℤ)
    (hb : ∀ i ∈ b.support, 0 < l (P.root i)) {i : J} (hi : b.IsPos i) :
    0 < l (P.root i) := by
  apply hi.induction_on_add hb
  intro a c z hz ha hc
  rw [hz, map_add]
  exact add_pos ha (hb c hc)

omit [P.IsReduced] in
private theorem isPos_iff_functional_pos (b : P.Base) (l : X →ₗ[ℤ] ℤ)
    (hb : ∀ i ∈ b.support, 0 < l (P.root i)) (i : J) :
    b.IsPos i ↔ 0 < l (P.root i) := by
  let := P.indexNeg
  constructor
  · exact functional_pos_of_isPos b l hb
  · intro hi
    rcases Base.IsPos.or_neg b i with h | h
    · exact h
    · have hn := functional_pos_of_isPos b l hb h
      change 0 < l (P.root (P.reflectionPerm i i)) at hn
      rw [P.root_reflectionPerm, P.reflection_apply_self, map_neg] at hn
      omega

omit [P.IsReduced] in
private theorem functional_ne_zero (b : P.Base) (l : X →ₗ[ℤ] ℤ)
    (hb : ∀ i ∈ b.support, 0 < l (P.root i)) (i : J) :
    l (P.root i) ≠ 0 := by
  let := P.indexNeg
  rcases Base.IsPos.or_neg b i with h | h
  · exact (functional_pos_of_isPos b l hb h).ne'
  · have hn := functional_pos_of_isPos b l hb h
    change 0 < l (P.root (P.reflectionPerm i i)) at hn
    rw [P.root_reflectionPerm, P.reflection_apply_self, map_neg] at hn
    exact (neg_pos.mp hn).ne

/-- The positive-coroot sum is strictly positive on every simple root. -/
private theorem exists_positive_functional (b : P.Base) :
    ∃ l : X →ₗ[ℤ] ℤ, ∀ i ∈ b.support, 0 < l (P.root i) := by
  classical
  let := Fintype.ofFinite J
  let s := Finset.univ.filter b.IsPos
  let l : X →ₗ[ℤ] ℤ := P.toLinearMap.flip (∑ j ∈ s, P.coroot j)
  refine ⟨l, fun i hi => ?_⟩
  have hpos : b.IsPos i := b.isPos_of_mem_support hi
  have hmem : i ∈ s := by simp [s, hpos]
  have hvalue : l (P.root i) = 2 := by
    change P.toLinearMap (P.root i) (∑ j ∈ s, P.coroot j) = 2
    rw [map_sum]
    rw [← Finset.add_sum_erase _ _ hmem, root_coroot_eq_pairing, pairing_same]
    simp only [root_coroot_eq_pairing]
    have hsum : ∑ j ∈ s.erase i, P.pairing i j = 0 := by
      have hinv : ∀ j, P.pairing i j + P.pairing i (P.reflectionPerm i j) = 0 := by
        intro j
        rw [pairing_reflectionPerm, pairing_reflectionPerm_self_left, add_neg_cancel]
      refine Finset.sum_involution (fun j _ => P.reflectionPerm i j)
        (fun j _ => hinv j) ?_ ?_ ?_
      · intro j _ hf heq
        apply hf
        have := hinv j
        rw [heq] at this
        omega
      · intro j hj
        simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          at hj ⊢
        refine ⟨fun h => ?_, hj.2.reflectionPerm hi hj.1⟩
        have hj' : j = P.reflectionPerm i i := by
          have := congrArg (P.reflectionPerm i) h
          rwa [reflectionPerm_self] at this
        have := (Base.IsPos.neg_iff_not b i).1
        rw [hj'] at hj
        exact this hj.2 hpos
      · intro j _
        exact reflectionPerm_self P i j
    rw [hsum, add_zero]
  rw [hvalue]
  norm_num

/-- An integral functional nonzero on roots defines a base with its prescribed signs. -/
private theorem exists_base_for_functional (q : X →ₗ[ℤ] ℤ)
    (hq : ∀ i, q (P.root i) ≠ 0) :
    ∃ b : P.Base, ∀ i, b.IsPos i ↔ 0 < q (P.root i) := by
  classical
  let := Fintype.ofFinite J
  let g : Module.Dual ℤ Y := q ∘ₗ P.CoPolarization
  have hg (i : J) : g (P.coroot i) ≠ 0 :=
    GroupScheme.SplitExistence.dual_polarization_root_ne_zero P.flip hq i
  have hqg (i : J) : 0 < q (P.root i) ↔ 0 < g (P.coroot i) :=
    (GroupScheme.SplitExistence.dual_polarization_root_pos_iff P.flip q i).symm
  have heq := GroupScheme.SplitExistence.baseOf_root_eq_baseOf_coroot P q g hq hg hqg
  let := P.indexNeg
  let b : P.Base := {
    support := (Set.toFinite (baseOf P.root (q : X →+ ℤ))).toFinset
    linearIndepOn_root := by
      simpa only [Set.Finite.coe_toFinset] using P.linearIndepOn_root_baseOf' q hq
    linearIndepOn_coroot := by
      rw [Set.Finite.coe_toFinset, heq]
      exact P.flip.linearIndepOn_root_baseOf' g hg
    root_mem_or_neg_mem := fun i => by
      simpa only [Set.Finite.coe_toFinset] using
        mem_or_neg_mem_closure_baseOf P.root (q : X →+ ℤ) i (hq i) (by simp)
    coroot_mem_or_neg_mem := fun i => by
      simpa only [Set.Finite.coe_toFinset, heq] using
        mem_or_neg_mem_closure_baseOf P.coroot (g : Y →+ ℤ) i (hg i) (by simp) }
  refine ⟨b, isPos_iff_functional_pos b q ?_⟩
  intro i hi
  have hm : i ∈ baseOf P.root (q : X →+ ℤ) := by
    simpa only [b, Set.Finite.mem_toFinset] using hi
  exact hm.1

omit [P.IsReduced] in
private theorem mem_support_iff_positive_indecomposable (b : P.Base) (i : J) :
    i ∈ b.support ↔ b.IsPos i ∧
      ∀ a c, b.IsPos a → b.IsPos c → P.root i ≠ P.root a + P.root c := by
  constructor
  · intro hi
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    intro a c ha hc heq
    have hh := b.height_add heq
    rw [b.height_one_of_mem_support hi] at hh
    change 0 < b.height a at ha
    change 0 < b.height c at hc
    omega
  · rintro ⟨hi, hindecomp⟩
    have h : i ∈ b.support ∨ ∃ a c, b.IsPos a ∧ b.IsPos c ∧
        P.root i = P.root a + P.root c := by
      apply hi.induction_on_add
      · intro j hj
        exact Or.inl hj
      · intro a c z hz ha hc
        refine Or.inr ⟨a, c, ?_, b.isPos_of_mem_support hc, hz⟩
        rcases ha with ha | ⟨d, e, hd, he, hde⟩
        · exact b.isPos_of_mem_support ha
        · exact hd.add he hde
    rcases h with h | ⟨a, c, ha, hc, heq⟩
    · exact h
    · exact False.elim (hindecomp a c ha hc heq)

/-- Simple roots are characterized by their action on the other positive roots. -/
private theorem mem_support_iff_reflection_pos
    (b : P.Base) (l : X →ₗ[ℤ] ℤ)
    (hsign : ∀ i, b.IsPos i ↔ 0 < l (P.root i)) (i : J) :
    i ∈ b.support ↔ 0 < l (P.root i) ∧
      ∀ j, 0 < l (P.root j) → j ≠ i →
        0 < l (P.reflection i (P.root j)) := by
  constructor
  · intro hi
    refine ⟨(hsign i).mp (b.isPos_of_mem_support hi), ?_⟩
    intro j hj hji
    rw [← P.root_reflectionPerm]
    exact (hsign _).mp (((hsign j).mpr hj).reflectionPerm hi hji)
  · rintro ⟨hi, hreflect⟩
    rw [mem_support_iff_positive_indecomposable]
    refine ⟨(hsign i).mpr hi, ?_⟩
    intro a c ha hc heq
    have ha' := (hsign a).mp ha
    have hc' := (hsign c).mp hc
    have hsum : l (P.root i) = l (P.root a) + l (P.root c) := by
      rw [heq, map_add]
    have hai : a ≠ i := by
      intro h
      subst a
      omega
    have hci : c ≠ i := by
      intro h
      subst c
      omega
    have hra := hreflect a ha' hai
    have hrc := hreflect c hc' hci
    have hr :
        l (P.reflection i (P.root a)) + l (P.reflection i (P.root c)) =
          -l (P.root i) := by
      rw [← map_add, ← map_add, ← heq, P.reflection_apply_self, map_neg]
    omega

end OneDatum

section Isogeny

variable {p : ℕ} {J : Type u₁} {X : Type u₂} {Y : Type u₃}
    {J' : Type u₄} {X' : Type u₅} {Y' : Type u₆}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Finite J] [Finite J']
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X'] [Module.Finite ℤ Y']
    {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
    [P.IsReduced] [Q.IsReduced]

private theorem weightMap_reflection (f : RootDatumIsogeny p P Q) (i : J) (x : X) :
    f.weightMap (P.reflection i x) =
      Q.reflection (f.indexEquiv i) (f.weightMap x) := by
  have hpair :
      (Q.coroot' (f.indexEquiv i)) (f.weightMap x) =
        (f.rootFactor i : ℤ) * (P.coroot' i) x := by
    change Q.toLinearMap (f.weightMap x) (Q.coroot (f.indexEquiv i)) =
      (f.rootFactor i : ℤ) * P.toLinearMap x (P.coroot i)
    rw [f.pairing_apply, f.coroot_coweightMap, map_smul, smul_eq_mul]
  simp only [RootPairing.reflection_apply, map_sub, map_smul,
    f.root_weightMap, hpair, smul_smul]
  rw [mul_comm]

private theorem root_pos_iff (f : RootDatumIsogeny p P Q) (l : X' →ₗ[ℤ] ℤ) (i : J) :
    0 < l (f.weightMap (P.root i)) ↔ 0 < l (Q.root (f.indexEquiv i)) := by
  rw [f.root_weightMap, map_smul, smul_eq_mul]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast f.rootFactor_pos i)

private theorem reflection_pos_iff (f : RootDatumIsogeny p P Q)
    (l : X' →ₗ[ℤ] ℤ) (i j : J) :
    0 < l (f.weightMap (P.reflection i (P.root j))) ↔
      0 < l (Q.reflection (f.indexEquiv i) (Q.root (f.indexEquiv j))) := by
  rw [weightMap_reflection, f.root_weightMap, map_smul, map_smul, smul_eq_mul]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast f.rootFactor_pos j)

private theorem support_iff (f : RootDatumIsogeny p P Q)
    (l : X' →ₗ[ℤ] ℤ) (b : P.Base) (b' : Q.Base)
    (hb : ∀ i, b.IsPos i ↔ 0 < l (f.weightMap (P.root i)))
    (hb' : ∀ j, b'.IsPos j ↔ 0 < l (Q.root j)) (i : J) :
    i ∈ b.support ↔ f.indexEquiv i ∈ b'.support := by
  rw [mem_support_iff_reflection_pos b (l.comp f.weightMap) hb,
    mem_support_iff_reflection_pos b' l hb']
  constructor
  · rintro ⟨hi, hr⟩
    refine ⟨(root_pos_iff f l i).mp hi, ?_⟩
    intro j hj hji
    let a := f.indexEquiv.symm j
    have hea : f.indexEquiv a = j := f.indexEquiv.apply_symm_apply j
    have ha : 0 < l (f.weightMap (P.root a)) :=
      (root_pos_iff f l a).mpr (by simpa only [hea] using hj)
    have hai : a ≠ i := by
      intro h
      apply hji
      rw [← hea, h]
    have h := (reflection_pos_iff f l i a).mp (hr a ha hai)
    simpa only [hea] using h
  · rintro ⟨hi, hr⟩
    refine ⟨(root_pos_iff f l i).mpr hi, ?_⟩
    intro j hj hji
    exact (reflection_pos_iff f l i j).mpr
      (hr (f.indexEquiv j) ((root_pos_iff f l j).mp hj)
        (fun h => hji (f.indexEquiv.injective h)))

end Isogeny

end RootDatumIsogenyBaseProof

open RootDatumIsogenyBaseProof in
/-- Conrad, Lemma 6.1.12, with all six type universes independent. -/
theorem rootDatumIsogenyBase :
    RootDatumIsogenyBaseStatement.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro p J X Y J' X' Y' _ _ _ _ _ _ _ _ _ _ P Q _ _ f b'
  obtain ⟨l, hl⟩ := exists_positive_functional b'
  have hsign := isPos_iff_functional_pos b' l hl
  have hreg (i : J) : (l.comp f.weightMap) (P.root i) ≠ 0 := by
    change l (f.weightMap (P.root i)) ≠ 0
    rw [f.root_weightMap, map_smul, smul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast (f.rootFactor_pos i).ne')
      (functional_ne_zero b' l hl _)
  obtain ⟨b, hb⟩ := exists_base_for_functional (P := P) (l.comp f.weightMap) hreg
  refine ⟨b, support_iff f l b b' hb hsign, ?_⟩
  intro i
  exact (hb i).trans ((root_pos_iff f l i).trans (hsign _).symm)

end Langlands.LinearAlgebra
