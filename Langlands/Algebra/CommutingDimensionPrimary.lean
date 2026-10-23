import Langlands.Algebra.CommutingDimensionNilpotent
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Analysis.MeanInequalitiesPow

/-! Primary-decomposition helpers for the commuting dimension estimate. -/

noncomputable section
open scoped BigOperators IsMulCommutative

namespace Langlands.CommutingDimension

universe uK uV

variable (K : Type uK) [Field K]

/-- Subtracting scalars from a generating family leaves its unital algebra unchanged. -/
theorem adjoin_shift_eq {E : Type*} [Ring E] [Algebra K E] {ι : Type*}
    (a : ι → E) (μ : ι → K) :
    Algebra.adjoin K (Set.range (fun i => a i - algebraMap K E (μ i))) =
      Algebra.adjoin K (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i))
      (Subalgebra.algebraMap_mem _ _)
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    have h := Subalgebra.add_mem
      (Algebra.adjoin K (Set.range (fun i => a i - algebraMap K E (μ i))))
      (Algebra.subset_adjoin (Set.mem_range_self i))
      (Subalgebra.algebraMap_mem _ (μ i))
    change a i - algebraMap K E (μ i) + algebraMap K E (μ i) ∈
      Algebra.adjoin K (Set.range (fun i => a i - algebraMap K E (μ i))) at h
    rw [sub_add_cancel] at h
    exact h

/-- Scalar shifts preserve pairwise commutation. -/
theorem commute_shift {E : Type*} [Ring E] [Algebra K E] {ι : Type*}
    (a : ι → E) (μ : ι → K) (hc : ∀ i j, Commute (a i) (a j)) :
    ∀ i j, Commute (a i - algebraMap K E (μ i)) (a j - algebraMap K E (μ j)) := by
  intro i j
  exact ((hc i j).sub_left (Algebra.commutes (μ i) (a j))).sub_right
    (Algebra.commutes (μ j) _).symm

/-- Real powers with exponent at least one are superadditive on finite sums. -/
theorem sum_rpow_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (r : ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hr : 1 ≤ r) :
    (∑ i ∈ s, x i ^ r) ≤ (∑ i ∈ s, x i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (by linarith : r ≠ 0)]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    apply (add_le_add le_rfl (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))).trans
    exact Real.add_rpow_le_rpow_add (hx i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => hx j (Finset.mem_insert_of_mem hj)) hr

variable (V : Type uV) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- An algebra acting on invariant subspaces which span is detected by all its restrictions. -/
theorem dimension_le_sum_restrictions
    (C : Subalgebra K (Module.End K V)) {ι : Type*} [Fintype ι]
    (W : ι → Submodule K V)
    (hW : ∀ i, ∀ c : C, ∀ v ∈ W i, c.val v ∈ W i)
    (hspan : ⨆ i, W i = ⊤) :
    Module.finrank K C ≤
      ∑ i, Module.finrank K (restrictionAlgHom K V C (W i) (hW i)).range := by
  let f i := restrictionAlgHom K V C (W i) (hW i)
  let : ∀ i, Module.Free K ((f i).range) := fun i => Module.Free.of_divisionRing K ((f i).range)
  let : ∀ i, Module.Finite K ((f i).range) := fun i => inferInstance
  let t : C →ₗ[K] ∀ i, (f i).range :=
    LinearMap.pi fun i => (f i).rangeRestrict.toLinearMap
  have hinj : Function.Injective t := by
    intro c d hcd
    have hker : (⊤ : Submodule K V) ≤ (c.val - d.val).ker := by
      rw [← hspan]
      apply iSup_le
      intro i v hv
      have hi : f i c = f i d := congrArg Subtype.val (congrFun hcd i)
      have heq := congrArg Subtype.val (LinearMap.congr_fun hi ⟨v, hv⟩)
      change c.val v - d.val v = 0
      exact sub_eq_zero.mpr heq
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact sub_eq_zero.mp (hker (Submodule.mem_top))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at h
  exact h

/-- Bounds on an independent invariant decomposition add to the same real-power bound. -/
theorem dimension_bound_of_decomposition
    (C : Subalgebra K (Module.End K V)) {ι : Type*} [Fintype ι]
    (W : ι → Submodule K V)
    (hW : ∀ i, ∀ c : C, ∀ v ∈ W i, c.val v ∈ W i)
    (hspan : ⨆ i, W i = ⊤) (hind : iSupIndep W) (r : ℝ) (hr : 1 ≤ r)
    (hbound : ∀ i, (Module.finrank K
      (restrictionAlgHom K V C (W i) (hW i)).range : ℝ) ≤
        (Module.finrank K (W i) : ℝ) ^ r) :
    (Module.finrank K C : ℝ) ≤ (Module.finrank K V : ℝ) ^ r := by
  classical
  have hdim : (∑ i, Module.finrank K (W i)) = Module.finrank K V := by
    have h := (hind.linearEquiv hspan).finrank_eq
    rw [← Module.finrank_directSum (R := K) (fun i => W i)]
    exact h
  have hreal : (∑ i, (Module.finrank K (W i) : ℝ)) = (Module.finrank K V : ℝ) := by
    exact_mod_cast hdim
  calc
    _ ≤ ∑ i, (Module.finrank K
        (restrictionAlgHom K V C (W i) (hW i)).range : ℝ) := by
      exact_mod_cast dimension_le_sum_restrictions K V C W hW hspan
    _ ≤ ∑ i, (Module.finrank K (W i) : ℝ) ^ r :=
      Finset.sum_le_sum fun i _ => hbound i
    _ ≤ (∑ i, (Module.finrank K (W i) : ℝ)) ^ r :=
      sum_rpow_le Finset.univ _ r (fun _ _ => Nat.cast_nonneg _) hr
    _ = _ := by rw [hreal]

set_option maxHeartbeats 800000 in
/-- The real dimension bound for commuting endomorphisms over an algebraically closed field. -/
theorem commuting_dimension [IsAlgClosed K] (l : ℕ)
    (a : Fin l → Module.End K V) (hc : ∀ i j, Commute (a i) (a j)) :
    (Module.finrank K (Algebra.adjoin K (Set.range a)) : ℝ) ≤
      (Module.finrank K V : ℝ) ^ dimensionExponent l := by
  classical
  cases l with
  | zero =>
    simpa only [dimensionExponent_zero, Real.rpow_zero, Nat.cast_le_one] using
      zero_generators K V a
  | succ l =>
    let C := Algebra.adjoin K (Set.range a)
    let : IsMulCommutative C := Algebra.isMulCommutative_adjoin K (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hc i j)
    let b : Fin (l + 1) → C := fun i =>
      ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
    have hb : Algebra.adjoin K (Set.range b) = ⊤ := adjoin_generators_top K a
    let W : (Fin (l + 1) → K) → Submodule K V := fun χ =>
      ⨅ i, (a i).maxGenEigenspace (χ i)
    have hind : iSupIndep W :=
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo a
        (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ)
    have htop : ⨆ χ, W χ = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        a (fun i j _ => hc i j) (fun i => (a i).iSup_maxGenEigenspace_eq_top)
    let I := {χ // W χ ≠ ⊥}
    let : Fintype I := hind.fintypeNeBotOfFiniteDimensional
    let U : I → Submodule K V := fun χ => W χ.val
    have hspan : ⨆ χ, U χ = ⊤ := by
      apply top_unique
      rw [← htop]
      apply iSup_le
      intro χ
      by_cases hχ : W χ = ⊥
      · rw [hχ]; exact bot_le
      · exact le_iSup U ⟨χ, hχ⟩
    have hU : ∀ χ, ∀ c : C, ∀ v ∈ U χ, c.val v ∈ U χ := by
      intro χ c v hv
      change v ∈ ⨅ i, (a i).maxGenEigenspace (χ.val i) at hv
      change c.val v ∈ ⨅ i, (a i).maxGenEigenspace (χ.val i)
      simp only [Submodule.mem_iInf] at hv ⊢
      intro i
      have hci : Commute (a i) c.val := congrArg Subtype.val (mul_comm (b i) c)
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hci _ (hv i)
    apply dimension_bound_of_decomposition K V C U hU hspan
      (hind.comp Subtype.val_injective) (dimensionExponent (l + 1))
      (dimensionExponent_succ_ge_one l)
    intro χ
    let f := restrictionAlgHom K V C (U χ) (hU χ)
    let aU : Fin (l + 1) → Module.End K (U χ) := fun i => f (b i)
    have haU : Algebra.adjoin K (Set.range aU) = f.range :=
      adjoin_image_generators K b hb f
    let n : Fin (l + 1) → Module.End K (U χ) := fun i =>
      aU i - algebraMap K (Module.End K (U χ)) (χ.val i)
    have hn : ∀ i, IsNilpotent (n i) := by
      intro i
      have hinv : Set.MapsTo (a i - algebraMap K (Module.End K V) (χ.val i))
          (U χ) (U χ) := by
        intro v hv
        exact (U χ).sub_mem (hU χ (b i) v hv) ((U χ).smul_mem _ hv)
      have heq : n i =
          (a i - algebraMap K (Module.End K V) (χ.val i)).restrict hinv := by
        ext v
        rfl
      rw [heq]
      exact Module.End.isNilpotent_restrict_of_le (iInf_le _ i)
        ((a i).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ.val i))
    have hncomm : ∀ i j, Commute (n i) (n j) :=
      commute_shift K aU χ.val (fun i j => (Commute.all (b i) (b j)).map f)
    have hbound := nilpotent_dimension K (l + 1) (U χ) n hncomm hn
    rw [adjoin_shift_eq K aU χ.val, haU] at hbound
    exact hbound

/-- Clearing the real exponent gives the natural-power commuting dimension estimate. -/
theorem commuting_dimension_nat [IsAlgClosed K] (l : ℕ)
    (a : Fin l → Module.End K V) (hc : ∀ i j, Commute (a i) (a j)) :
    Module.finrank K (Algebra.adjoin K (Set.range a)) ^ (2 ^ l) ≤
      Module.finrank K V ^ (2 ^ (l + 1) - 2) := by
  have h := Real.rpow_le_rpow (Nat.cast_nonneg
    (Module.finrank K (Algebra.adjoin K (Set.range a))))
    (commuting_dimension K V l a hc) (Nat.cast_nonneg (2 ^ l))
  have htwo : 2 ≤ 2 ^ (l + 1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := l)
    omega
  have he : dimensionExponent l * ((2 ^ l : ℕ) : ℝ) =
      ((2 ^ (l + 1) - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub htwo]
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, dimensionExponent, pow_succ]
    field_simp
  rw [← Real.rpow_mul (Nat.cast_nonneg (Module.finrank K V)), he,
    Real.rpow_natCast, Real.rpow_natCast] at h
  exact_mod_cast h

end Langlands.CommutingDimension
