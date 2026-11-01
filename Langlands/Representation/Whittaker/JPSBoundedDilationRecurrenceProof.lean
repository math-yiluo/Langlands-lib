import Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Proof of the uniform-region recurrence for powers of a bounded coordinate dilation

The ascending chain of spans of the first powers `σ_i(c ^ j)` in the finite operator
span stabilizes, which gives one length `D` and scalar coefficients `d m j` with
`σ_i(c ^ m) = ∑ j < D, d m j • σ_i(c ^ j)`. For one `f`, the relation for `m = D`
vanishes below a threshold that bounded dilations preserve, so all powers `ρ_i(c ^ m) f`
lie in the span of the first `D` powers plus functions vanishing below it; the finite
span meets the coordinate-vanishing space in a finite-dimensional space with one common
threshold. See the paired Markdown for the route.
-/

noncomputable section

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

namespace JPSBoundedDilationRecurrenceProof

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

theorem normalizedAbs_pow_le_one (T : F.TopologicalData) {c : F.Carrierˣ}
    (hc : T.normalizedAbs (c : F.Carrier) ≤ 1) (m : ℕ) :
    T.normalizedAbs ((c ^ m : F.Carrierˣ) : F.Carrier) ≤ 1 := by
  induction m with
  | zero => simp [T.normalizedAbs_one]
  | succ m ih =>
    rw [pow_succ, Units.val_mul, T.normalizedAbs_mul]
    exact (mul_le_of_le_one_left (T.normalizedAbs_nonneg _) ih).trans hc

/-- A uniform threshold for finitely many threshold properties closed under shrinking. -/
theorem exists_common_threshold {ι : Type*} (s : Finset ι) (P : ι → ℝ → Prop)
    (hP : ∀ j δ δ', 0 < δ' → δ' ≤ δ → P j δ → P j δ')
    (h : ∀ j ∈ s, ∃ δ : ℝ, 0 < δ ∧ P j δ) : ∃ δ : ℝ, 0 < δ ∧ ∀ j ∈ s, P j δ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | insert j s hj ih =>
    obtain ⟨δ, hδ, hs⟩ := ih fun l hl => h l (Finset.mem_insert_of_mem hl)
    obtain ⟨δ', hδ', hj'⟩ := h j (Finset.mem_insert_self j s)
    refine ⟨min δ δ', lt_min hδ hδ', fun l hl => ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hP l δ' _ (lt_min hδ hδ') (min_le_right _ _) hj'
    · exact hP l δ _ (lt_min hδ hδ') (min_le_left _ _) (hs l hl)

section SmallVanishing

variable {n : ℕ} (W : FunctionSpace F n) (T : F.TopologicalData) (i : Fin n)

/-- Functions vanishing at every torus point whose `i`th coordinate is below `δ`. -/
def smallVanishing (δ : ℝ) : Submodule ℂ W.toSubmodule where
  carrier := {h | ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < δ → h.val a = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {f g} hf hg a ha => by
    change f.val a + g.val a = 0
    rw [hf a ha, hg a ha, add_zero]
  smul_mem' := fun c f hf a ha => by
    change c * f.val a = 0
    rw [hf a ha, mul_zero]

theorem mem_smallVanishing_iff (δ : ℝ) (h : W.toSubmodule) :
    h ∈ smallVanishing W T i δ ↔
      ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < δ → h.val a = 0 := Iff.rfl

theorem smallVanishing_anti {δ δ' : ℝ} (hle : δ' ≤ δ) :
    smallVanishing W T i δ ≤ smallVanishing W T i δ' := by
  intro h hh
  rw [mem_smallVanishing_iff] at hh ⊢
  exact fun a ha => hh a (lt_of_lt_of_le ha hle)

theorem germMap_eq_zero_of_mem_smallVanishing {δ : ℝ} (hδ : 0 < δ) {h : W.toSubmodule}
    (hh : h ∈ smallVanishing W T i δ) : germMap W T i h = 0 :=
  (germMap_eq_zero_iff W T i h).mpr ⟨δ, hδ, hh⟩

theorem exists_mem_smallVanishing {h : W.toSubmodule} (hh : germMap W T i h = 0) :
    ∃ δ : ℝ, 0 < δ ∧ h ∈ smallVanishing W T i δ :=
  (germMap_eq_zero_iff W T i h).mp hh

/-- Bounded coordinate dilations preserve vanishing below a fixed threshold. -/
theorem coordinateRepresentation_mem_smallVanishing {δ : ℝ} {c : F.Carrierˣ}
    (hc : T.normalizedAbs (c : F.Carrier) ≤ 1) {h : W.toSubmodule}
    (hh : h ∈ smallVanishing W T i δ) :
    coordinateRepresentation W i c h ∈ smallVanishing W T i δ := by
  rw [mem_smallVanishing_iff] at hh ⊢
  intro a ha
  rw [coordinateRepresentation_apply]
  apply hh
  rw [Pi.mul_apply, coordinateEmbedding_same, Units.val_mul, T.normalizedAbs_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (T.normalizedAbs_nonneg _) hc) ha

/-- A finite-dimensional space of functions with zero germs has one common threshold. -/
theorem exists_threshold_of_finiteDimensional (P : Submodule ℂ W.toSubmodule)
    [FiniteDimensional ℂ P] (hP : ∀ h ∈ P, germMap W T i h = 0) :
    ∃ δ : ℝ, 0 < δ ∧ P ≤ smallVanishing W T i δ := by
  classical
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional P).mpr inferInstance
  obtain ⟨δ, hδ, hδt⟩ := exists_common_threshold t
    (fun h δ => h ∈ smallVanishing W T i δ)
    (fun _ _ _ _ hle hh => smallVanishing_anti W T i hle hh)
    (fun h hh => exists_mem_smallVanishing W T i (hP h (by
      rw [← ht]
      exact Submodule.subset_span hh)))
  refine ⟨δ, hδ, ?_⟩
  rw [← ht]
  exact Submodule.span_le.mpr fun h hh => hδt h hh

/-- A relation among the first powers of a bounded dilation propagates to all its powers,
modulo functions vanishing below the threshold of that relation. -/
theorem pow_mem_sup {c : F.Carrierˣ} (hc : T.normalizedAbs (c : F.Carrier) ≤ 1)
    (D : ℕ) (e : Fin D → ℂ) (g : W.toSubmodule) {δ : ℝ}
    (hrel : coordinateRepresentation W i (c ^ D) g -
      ∑ j : Fin D, e j • coordinateRepresentation W i (c ^ (j : ℕ)) g ∈
        smallVanishing W T i δ) (m : ℕ) :
    coordinateRepresentation W i (c ^ m) g ∈
      Submodule.span ℂ (Set.range fun j : Fin D =>
        coordinateRepresentation W i (c ^ (j : ℕ)) g) ⊔ smallVanishing W T i δ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_cases hm : m < D
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩)
  · obtain ⟨s, rfl⟩ : ∃ s, m = s + D := ⟨m - D, by omega⟩
    have hz := coordinateRepresentation_mem_smallVanishing W T i
      (normalizedAbs_pow_le_one T hc s) hrel
    have hpow : ∀ k : ℕ, coordinateRepresentation W i (c ^ s)
        (coordinateRepresentation W i (c ^ k) g) =
          coordinateRepresentation W i (c ^ (s + k)) g := by
      intro k
      rw [← Module.End.mul_apply, ← map_mul, ← pow_add]
    have heq : coordinateRepresentation W i (c ^ (s + D)) g =
        coordinateRepresentation W i (c ^ s)
            (coordinateRepresentation W i (c ^ D) g -
              ∑ j : Fin D, e j • coordinateRepresentation W i (c ^ (j : ℕ)) g) +
          ∑ j : Fin D, e j • coordinateRepresentation W i (c ^ (s + (j : ℕ))) g := by
      rw [map_sub, map_sum, hpow D]
      simp only [map_smul, hpow, sub_add_cancel]
    rw [heq]
    refine add_mem (Submodule.mem_sup_right hz) (sum_mem fun j _ => ?_)
    have hj := j.isLt
    exact Submodule.smul_mem _ _ (ih _ (by omega))

end SmallVanishing

section OperatorRecurrence

variable {n : ℕ} (W : FunctionSpace F n) (T : F.TopologicalData) (i : Fin n)

/-- In a finite operator span, all powers of `σ(c)` lie in the span of the first `D`. -/
theorem exists_pow_mem_span (hS : HasFiniteCoordinateOperatorSpan W T i) (c : F.Carrierˣ) :
    ∃ D : ℕ, ∀ m : ℕ, sigma W T i (c ^ m) ∈
      Submodule.span ℂ (Set.range fun j : Fin D => sigma W T i (c ^ (j : ℕ))) := by
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (sigma W T i))) := hS
  let S := Submodule.span ℂ (Set.range (sigma W T i))
  let τ : F.Carrierˣ → S := fun b => ⟨sigma W T i b, Submodule.subset_span ⟨b, rfl⟩⟩
  let N : ℕ →o Submodule ℂ S :=
    { toFun := fun d => Submodule.span ℂ (Set.range fun j : Fin d => τ (c ^ (j : ℕ)))
      monotone' := fun d d' h => Submodule.span_mono (by
        rintro _ ⟨j, rfl⟩
        exact ⟨Fin.castLE h j, rfl⟩) }
  have : IsNoetherian ℂ S := (IsNoetherian.iff_fg (K := ℂ) (V := S)).mpr inferInstance
  obtain ⟨D, hD⟩ := monotone_stabilizes_iff_noetherian.mpr this N
  refine ⟨D, fun m => ?_⟩
  have hmem : τ (c ^ m) ∈ N D := by
    by_cases hm : m < D
    · exact Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
    · rw [hD (m + 1) (by omega)]
      exact Submodule.subset_span ⟨Fin.last m, rfl⟩
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [Submodule.mem_span_range_iff_exists_fun ℂ]
  refine ⟨e, ?_⟩
  have h2 := congrArg Subtype.val he
  rw [Submodule.coe_sum] at h2
  simpa only [Submodule.coe_smul] using h2

end OperatorRecurrence

/-- The uniform-region recurrence for one actual space, coordinate and bounded unit. -/
theorem recurrence_of_finiteSpan (T : F.TopologicalData) {n : ℕ} (W : FunctionSpace F n)
    (i : Fin n) (hS : HasFiniteCoordinateOperatorSpan W T i) (c : F.Carrierˣ)
    (hc : T.normalizedAbs (c : F.Carrier) ≤ 1) :
    ∃ (D : ℕ) (d : ℕ → Fin D → ℂ),
      ∀ f : W.toSubmodule,
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (m : ℕ) (a : Torus F n),
            T.normalizedAbs (a i : F.Carrier) < δ →
              (coordinateRepresentation W i (c ^ m) f).val a =
                ∑ j : Fin D, d m j * (coordinateRepresentation W i (c ^ (j : ℕ)) f).val a := by
  classical
  obtain ⟨D, hD⟩ := exists_pow_mem_span W T i hS c
  choose d hd using fun m => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hD m)
  refine ⟨D, d, fun f => ?_⟩
  have hgerm : ∀ m : ℕ, germMap W T i (coordinateRepresentation W i (c ^ m) f -
      ∑ j : Fin D, d m j • coordinateRepresentation W i (c ^ (j : ℕ)) f) = 0 := by
    intro m
    rw [map_sub, map_sum, ← sigma_apply_mk, ← hd m, LinearMap.sum_apply, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, map_smul, sigma_apply_mk]
  obtain ⟨δ₁, hδ₁, hrel⟩ := exists_mem_smallVanishing W T i (hgerm D)
  let G : Fin D → W.toSubmodule := fun j => coordinateRepresentation W i (c ^ (j : ℕ)) f
  let L : Submodule ℂ W.toSubmodule := Submodule.span ℂ (Set.range G)
  have : FiniteDimensional ℂ L := FiniteDimensional.span_of_finite ℂ (Set.finite_range G)
  let P : Submodule ℂ W.toSubmodule := L ⊓ (coordinateVanishing W T i).toSubmodule
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨δ₂, hδ₂, hP⟩ := exists_threshold_of_finiteDimensional W T i P
    (fun h hh => (germMap_eq_zero_iff W T i h).mpr (Submodule.mem_inf.mp hh).2)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun m a ha => ?_⟩
  have haδ₁ : T.normalizedAbs (a i : F.Carrier) < δ₁ := lt_of_lt_of_le ha (min_le_left _ _)
  have haδ₂ : T.normalizedAbs (a i : F.Carrier) < δ₂ := lt_of_lt_of_le ha (min_le_right _ _)
  have hH : coordinateRepresentation W i (c ^ m) f -
      ∑ j : Fin D, d m j • coordinateRepresentation W i (c ^ (j : ℕ)) f ∈
        L ⊔ smallVanishing W T i δ₁ :=
    sub_mem (pow_mem_sup W T i hc D (d D) f hrel m)
      (Submodule.mem_sup_left (sum_mem fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
  obtain ⟨z, hz, e, he, hze⟩ := Submodule.mem_sup.mp hH
  have he0 : germMap W T i e = 0 := germMap_eq_zero_of_mem_smallVanishing W T i hδ₁ he
  have hzP : z ∈ P := by
    refine Submodule.mem_inf.mpr ⟨hz, ?_⟩
    change VanishesNearCoordinateZero T i z.val
    rw [← germMap_eq_zero_iff, eq_sub_of_add_eq hze, map_sub, hgerm m, he0, sub_zero]
  have hz2 := (mem_smallVanishing_iff W T i δ₂ z).mp (hP hzP) a haδ₂
  have he2 := (mem_smallVanishing_iff W T i δ₁ e).mp he a haδ₁
  have hval := congrArg (fun h : W.toSubmodule => h.val a) hze
  simp only [Submodule.coe_add, Pi.add_apply, hz2, he2, add_zero, Submodule.coe_sub,
    Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at hval
  exact (sub_eq_zero.mp hval.symm)

end JPSBoundedDilationRecurrenceProof

/-- The uniform-region recurrence for powers of a bounded coordinate dilation. -/
theorem jpsBoundedDilationRecurrence : JPSBoundedDilationRecurrenceStatement.{uF} := by
  intro p _ F T n W i hS c hc
  exact JPSBoundedDilationRecurrenceProof.recurrence_of_finiteSpan T W i hS c hc

end Langlands.Whittaker
