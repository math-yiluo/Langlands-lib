import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Bases of reduced root data over `ℤ`

Mathlib proves the existence of a base (`RootPairing.nonempty_base`) for reduced crystallographic
root systems over a field of characteristic zero. This file proves the same for a reduced root
datum `P : RootDatum J X Y` with finite index type, where the roots need not span `X`. The base
is `baseOf P.root f` for the functional `f = g ∘ P.Polarization`, where `g : Y → ℤ` is nonzero
on every coroot.
-/

namespace Langlands.GroupScheme.SplitExistence

open RootPairing Set IsAddIndecomposable Module

section RootForm

variable {J X Y : Type*} [Fintype J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

lemma rootForm_comm (x y : X) : P.RootForm x y = P.RootForm y x := by
  simp only [rootForm_apply_apply, mul_comm]

lemma rootForm_self_nonneg (x : X) : 0 ≤ P.RootForm x x := by
  rw [rootForm_apply_apply]
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

lemma four_le_rootForm_root (j : J) : 4 ≤ P.RootForm (P.root j) (P.root j) := by
  rw [rootForm_root_self]
  have h := Finset.single_le_sum (f := fun i ↦ P.pairing j i * P.pairing j i)
    (fun i _ ↦ mul_self_nonneg _) (Finset.mem_univ j)
  simp only [pairing_same] at h
  linarith

/-- `2 B(x, α) = ⟨x, α^∨⟩ B(α, α)`. -/
lemma two_mul_rootForm_root (x : X) (j : J) :
    2 * P.RootForm x (P.root j) =
      P.toLinearMap x (P.coroot j) * P.RootForm (P.root j) (P.root j) := by
  have h := congrArg (P.toLinearMap x) (P.rootForm_self_smul_coroot j)
  rw [map_smul, map_nsmul, toLinearMap_apply_apply_Polarization, smul_eq_mul, nsmul_eq_mul] at h
  rw [rootForm_comm P x (P.root j)]
  push_cast at h
  linarith

/-- An element of the root span with zero canonical norm is zero. -/
lemma eq_zero_of_mem_rootSpan {z : X} (hz : z ∈ P.rootSpan ℤ) (h : P.RootForm z z = 0) :
    z = 0 := by
  by_contra hne
  have hx : (⟨z, hz⟩ : P.rootSpan ℤ) ≠ 0 := by
    intro h0
    exact hne (congrArg Subtype.val h0)
  obtain ⟨i, hi⟩ := P.exists_coroot_ne ℤ hx
  have hi' : P.coroot' i z ≠ 0 := by
    have := algebraMap_coroot'In_apply P ℤ i ⟨z, hz⟩
    rw [Algebra.algebraMap_self_apply] at this
    rwa [← this]
  have hle := Finset.single_le_sum (f := fun m ↦ P.coroot' m z * P.coroot' m z)
    (fun m _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
  rw [rootForm_apply_apply] at h
  rw [h] at hle
  exact hi' (mul_self_eq_zero.mp (le_antisymm hle (mul_self_nonneg _)))

end RootForm

/-- Finitely many vectors, each detected by some integral functional, are detected
simultaneously by a single integral functional. -/
lemma exists_dual_forall_ne_zero {ι M : Type*} [AddCommGroup M] (s : Finset ι) (v : ι → M)
    (h : ∀ i ∈ s, ∃ φ : Dual ℤ M, φ (v i) ≠ 0) : ∃ φ : Dual ℤ M, ∀ i ∈ s, φ (v i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨φ, hφ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ψ, hψ⟩ := h j (Finset.mem_insert_self j s)
    have hpair : ∀ i ∈ insert j s, φ (v i) ≠ 0 ∨ ψ (v i) ≠ 0 := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inr hψ
      · exact Or.inl (hφ i hi)
    have hsub : ∀ i ∈ insert j s, {n : ℤ | φ (v i) + n * ψ (v i) = 0}.Subsingleton := by
      intro i hi n₁ hn₁ n₂ hn₂
      simp only [Set.mem_ofPred_eq] at hn₁ hn₂
      have h12 : (n₁ - n₂) * ψ (v i) = 0 := by linear_combination hn₁ - hn₂
      rcases mul_eq_zero.mp h12 with h0 | h0
      · exact sub_eq_zero.mp h0
      · rcases hpair i hi with h' | h'
        · exact absurd (by simpa [h0] using hn₁) h'
        · exact absurd h0 h'
    have hfin : (⋃ i ∈ (insert j s : Finset ι),
        {n : ℤ | φ (v i) + n * ψ (v i) = 0}).Finite :=
      (insert j s).finite_toSet.biUnion fun i hi ↦ (hsub i hi).finite
    obtain ⟨n, hn⟩ := hfin.infinite_compl.nonempty
    refine ⟨φ + n • ψ, fun i hi hzero ↦ hn ?_⟩
    simp only [mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨i, hi, ?_⟩
    simpa [smul_eq_mul] using hzero

variable {J X Y : Type*} [Fintype J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

/-- An integral functional on `Y` which is nonzero on every coroot. -/
lemma exists_dual_coroot_ne_zero : ∃ g : Dual ℤ Y, ∀ i, g (P.coroot i) ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_dual_forall_ne_zero Finset.univ P.coroot fun i _ ↦
    ⟨P.toLinearMap (P.root i), by simp [root_coroot_eq_pairing, pairing_same]⟩
  exact ⟨g, fun i ↦ hg i (Finset.mem_univ i)⟩

/-- `2 g(Pol α) = B(α, α) g(α^∨)`. -/
lemma two_mul_dual_polarization_root (g : Dual ℤ Y) (i : J) :
    2 * g (P.Polarization (P.root i)) = P.RootForm (P.root i) (P.root i) * g (P.coroot i) := by
  have h := congrArg g (P.rootForm_self_smul_coroot i)
  rw [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linarith

lemma dual_polarization_root_pos_iff (g : Dual ℤ Y) (i : J) :
    0 < g (P.Polarization (P.root i)) ↔ 0 < g (P.coroot i) := by
  have h := two_mul_dual_polarization_root P g i
  have hl := four_le_rootForm_root P i
  constructor
  · intro hp
    by_contra! hn
    nlinarith
  · intro hp
    nlinarith

lemma dual_polarization_root_ne_zero {g : Dual ℤ Y} (hg : ∀ i, g (P.coroot i) ≠ 0) (i : J) :
    g (P.Polarization (P.root i)) ≠ 0 := by
  have h := two_mul_dual_polarization_root P g i
  have hl := four_le_rootForm_root P i
  intro h0
  rw [h0, mul_zero] at h
  rcases mul_eq_zero.mp h.symm with h' | h'
  · linarith
  · exact hg i h'

/-- Integral version of `RootPairing.baseOf_root_eq_baseOf_coroot_aux`. -/
lemma baseOf_root_subset_baseOf_coroot [P.IsReduced] (f : Dual ℤ X) (g : Dual ℤ Y)
    (hf : ∀ i, f (P.root i) ≠ 0) (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root (f : X →+ ℤ) ⊆ baseOf P.coroot (g : Y →+ ℤ) := by
  classical
  let s := baseOf P.root (f : X →+ ℤ)
  intro i hi
  have hi0 : 0 < f (P.root i) := hi.1
  refine ⟨(hfg i).mp hi0, fun j hj k hk hijk ↦ ?_⟩
  have hj0 : 0 < f (P.root j) := (hfg j).mpr hj
  have hk0 : 0 < f (P.root k) := (hfg k).mpr hk
  let l : J → ℤ := fun m ↦ P.RootForm (P.root m) (P.root m)
  have hl : ∀ m, 0 < l m := fun m ↦ by have := four_le_rootForm_root P m; simp only [l]; omega
  -- the coroot relation gives a root relation
  have hrel : (l j * l k) • P.root i = (l i * l k) • P.root j + (l i * l j) • P.root k := by
    let z := (l j * l k) • P.root i - (l i * l k) • P.root j - (l i * l j) • P.root k
    have hz : z ∈ P.rootSpan ℤ := by
      have hm : ∀ m, P.root m ∈ P.rootSpan ℤ := fun m ↦ Submodule.subset_span (mem_range_self m)
      exact sub_mem (sub_mem (Submodule.smul_mem _ _ (hm i)) (Submodule.smul_mem _ _ (hm j)))
        (Submodule.smul_mem _ _ (hm k))
    have e1 : P.RootForm z z = (l j * l k) * P.RootForm z (P.root i) -
        (l i * l k) * P.RootForm z (P.root j) - (l i * l j) * P.RootForm z (P.root k) := by
      calc P.RootForm z z = P.RootForm z ((l j * l k) • P.root i - (l i * l k) • P.root j -
            (l i * l j) • P.root k) := rfl
        _ = _ := by simp only [map_sub, map_smul, smul_eq_mul]
    have hc : P.toLinearMap z (P.coroot i) =
        P.toLinearMap z (P.coroot j) + P.toLinearMap z (P.coroot k) := by
      rw [hijk, map_add]
    have hi' := two_mul_rootForm_root P z i
    have hj' := two_mul_rootForm_root P z j
    have hk' := two_mul_rootForm_root P z k
    have hB : 2 * P.RootForm z z = 0 := by
      linear_combination 2 * e1 + (l j * l k) * hi' - (l i * l k) * hj' - (l i * l j) * hk' +
        (l i * l j * l k) * hc
    have h0 : (l j * l k) • P.root i - (l i * l k) • P.root j - (l i * l j) • P.root k = 0 :=
      eq_zero_of_mem_rootSpan P hz (by linarith)
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  -- write `α_j` and `α_k` as nonnegative combinations of the simple roots
  have hjk : ∀ {m : J}, 0 < g (P.coroot m) →
      ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : X) = P.root m := by
    intro m hm
    have hm' : 0 < (f : X →+ ℤ) (P.root m) := (hfg m).mpr hm
    rwa [← Submodule.mem_span_iff_of_fintype, ← Submodule.mem_toAddSubmonoid,
      Submodule.span_nat_eq_addSubmonoidClosure,
      AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
      AddSubmonoid.mem_closure_image_pos_iff P.root (f : X →+ ℤ) _ (P.ne_zero _)]
  obtain ⟨a, ha⟩ := hjk hj
  obtain ⟨c, hc⟩ := hjk hk
  let ri : P.root '' s := ⟨P.root i, mem_image_of_mem _ hi⟩
  have hli : LinearIndepOn ℤ id (P.root '' s) := by
    rw [← linearIndepOn_iff_image P.root.injective.injOn]
    exact linearIndepOn_root_baseOf' P (S := ℤ) f hf
  rw [← linearIndependent_subtype_iff] at hli
  have hcoef : (fun x ↦ (l i * l k) * (a x : ℤ) + (l i * l j) * (c x : ℤ)) =
      Pi.single ri (l j * l k) := by
    apply linearIndependent_iff_injective_fintypeLinearCombination.mp hli
    simp only [Fintype.linearCombination_apply]
    calc ∑ x : P.root '' s, ((l i * l k) * (a x : ℤ) + (l i * l j) * (c x : ℤ)) • (x : X)
        = (l i * l k) • ∑ x, a x • (x : X) + (l i * l j) • ∑ x, c x • (x : X) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, mul_smul,
            Nat.cast_smul_eq_nsmul]
      _ = (l j * l k) • P.root i := by rw [ha, hc, ← hrel]
      _ = ∑ x : P.root '' s, (Pi.single ri (l j * l k) : P.root '' s → ℤ) x • (x : X) := by
          rw [Fintype.sum_eq_single ri (fun x hx ↦ by simp [hx])]
          simp [ri]
  have ha0 : ∀ x, x ≠ ri → a x = 0 := by
    intro x hx
    have h := congrFun hcoef x
    simp only [Pi.single_apply, hx, ite_false] at h
    have h1 : 0 ≤ (l i * l k) * (a x : ℤ) :=
      mul_nonneg (mul_pos (hl i) (hl k)).le (Int.natCast_nonneg _)
    have h2 : 0 ≤ (l i * l j) * (c x : ℤ) :=
      mul_nonneg (mul_pos (hl i) (hl j)).le (Int.natCast_nonneg _)
    have h3 : (l i * l k) * (a x : ℤ) = 0 := by omega
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (mul_pos (hl i) (hl k)).ne'
    · exact_mod_cast h4
  have hji : P.root j = a ri • P.root i := by
    rw [← ha, Fintype.sum_eq_single ri (fun x hx ↦ by simp [ha0 x hx])]
  have hind : LinearIndependent ℤ ![P.root i, P.root j] := by
    refine IsReduced.linearIndependent P (fun hij ↦ ?_) (fun hij ↦ ?_)
    · subst hij
      exact P.ne_zero' k (by simpa using hijk)
    · have := congrArg f hij
      rw [map_neg] at this
      omega
  rw [LinearIndependent.pair_iff] at hind
  have := hind (a ri : ℤ) (-1) (by rw [hji]; simp [Nat.cast_smul_eq_nsmul])
  omega

/-- Integral version of `RootPairing.baseOf_root_eq_baseOf_coroot`. -/
lemma baseOf_root_eq_baseOf_coroot [P.IsReduced] (f : Dual ℤ X) (g : Dual ℤ Y)
    (hf : ∀ i, f (P.root i) ≠ 0) (hg : ∀ i, g (P.coroot i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root (f : X →+ ℤ) = baseOf P.coroot (g : Y →+ ℤ) := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : IsReflexive ℤ Y := .of_isPerfPair P.flip.toLinearMap
  exact subset_antisymm (baseOf_root_subset_baseOf_coroot P f g hf hfg)
    (baseOf_root_subset_baseOf_coroot P.flip g f hg fun i ↦ (hfg i).symm)

/-- A reduced root datum with finitely many roots has a base. -/
theorem nonempty_base_int {J X Y : Type*} [Finite J] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) [P.IsReduced] : Nonempty P.Base := by
  have := Fintype.ofFinite J
  obtain ⟨g, hg⟩ := exists_dual_coroot_ne_zero P
  let f : Dual ℤ X := g ∘ₗ P.Polarization
  have hf : ∀ i, f (P.root i) ≠ 0 := dual_polarization_root_ne_zero P hg
  have hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i) := dual_polarization_root_pos_iff P g
  have heq := baseOf_root_eq_baseOf_coroot P f g hf hg hfg
  let := P.indexNeg
  exact ⟨{ support := (toFinite (baseOf P.root (f : X →+ ℤ))).toFinset
           linearIndepOn_root := by simpa using linearIndepOn_root_baseOf' P (S := ℤ) f hf
           linearIndepOn_coroot := by
             simpa [heq] using linearIndepOn_root_baseOf' P.flip (S := ℤ) g hg
           root_mem_or_neg_mem := fun i ↦ by
             simpa using mem_or_neg_mem_closure_baseOf P.root (f : X →+ ℤ) i (hf i) (by simp)
           coroot_mem_or_neg_mem := fun i ↦ by
             simpa [heq] using
               mem_or_neg_mem_closure_baseOf P.coroot (g : Y →+ ℤ) i (hg i) (by simp) }⟩

end Langlands.GroupScheme.SplitExistence
