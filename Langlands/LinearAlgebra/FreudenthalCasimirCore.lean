import Langlands.LinearAlgebra.FreudenthalCasimirAlgebra

/-! # Freudenthal's recursion from the Casimir element

This module proves `FreudenthalCasimirCoreStatement`. The Casimir element of
`FreudenthalCasimirAlgebra` acts on the irreducible subspace `V` by a scalar. Comparing its
trace on each `V ⊓ W μ` with the traces of its torus and root parts, and telescoping the traces
of the products `e_i f_i` along the root strings, gives Freudenthal's identity. -/

noncomputable section

open Module Function Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.LinearAlgebra.FreudenthalCasimir

open WeightGraded

section TraceOn

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U] [FiniteDimensional k U]

/-- The trace of an endomorphism on a subspace it preserves (zero if it does not). -/
def trOn (V : Submodule k U) (z : Module.End k U) : k := by
  classical
  exact if hz : ∀ v ∈ V, z v ∈ V then LinearMap.trace k V (z.restrict hz) else 0

omit [FiniteDimensional k U] in
theorem trOn_eq {V : Submodule k U} {z : Module.End k U} (hz : ∀ v ∈ V, z v ∈ V) :
    trOn V z = LinearMap.trace k V (z.restrict hz) := by
  rw [trOn, dite_eq_left hz]

omit [FiniteDimensional k U] in
theorem trOn_add {V : Submodule k U} {z z' : Module.End k U} (hz : ∀ v ∈ V, z v ∈ V)
    (hz' : ∀ v ∈ V, z' v ∈ V) : trOn V (z + z') = trOn V z + trOn V z' := by
  have hzz : ∀ v ∈ V, (z + z') v ∈ V := fun v hv => V.add_mem (hz v hv) (hz' v hv)
  rw [trOn_eq hzz, trOn_eq hz, trOn_eq hz', ← map_add]
  congr 1

omit [FiniteDimensional k U] in
theorem trOn_zero (V : Submodule k U) : trOn V 0 = 0 := by
  have h0 : ∀ v ∈ V, (0 : Module.End k U) v ∈ V := fun v _ => V.zero_mem
  rw [trOn_eq h0]
  have : (0 : Module.End k U).restrict h0 = 0 := LinearMap.ext fun v => Subtype.ext rfl
  rw [this, map_zero]

omit [FiniteDimensional k U] in
theorem trOn_sum {V : Submodule k U} {κ : Type*} (s : Finset κ) {z : κ → Module.End k U}
    (hz : ∀ a ∈ s, ∀ v ∈ V, z a v ∈ V) : trOn V (∑ a ∈ s, z a) = ∑ a ∈ s, trOn V (z a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trOn_zero]
  | insert a s ha ih =>
    have hs : ∀ v ∈ V, (∑ b ∈ s, z b) v ∈ V := by
      intro v hv
      rw [LinearMap.sum_apply]
      exact V.sum_mem fun b hb => hz b (Finset.mem_insert_of_mem hb) v hv
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      trOn_add (hz a (Finset.mem_insert_self a s)) hs,
      ih fun b hb => hz b (Finset.mem_insert_of_mem hb)]

theorem trOn_eq_mul_finrank {V : Submodule k U} {z : Module.End k U} {c : k}
    (hz : ∀ v ∈ V, z v = c • v) : trOn V z = c * finrank k V := by
  have hmaps : ∀ v ∈ V, z v ∈ V := fun v hv => by rw [hz v hv]; exact V.smul_mem c hv
  rw [trOn_eq hmaps]
  have : z.restrict hmaps = c • LinearMap.id := LinearMap.ext fun v => Subtype.ext (hz v v.2)
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]

omit [FiniteDimensional k U] in
theorem trOn_eq_zero_of_eq_bot {V : Submodule k U} (hV : V = ⊥) (z : Module.End k U) :
    trOn V z = 0 := by
  by_cases hz : ∀ v ∈ V, z v ∈ V
  · rw [trOn_eq hz]
    have : z.restrict hz = 0 :=
      LinearMap.ext fun v => Subtype.ext ((Submodule.eq_bot_iff V).mp hV _ (hz v v.2))
    rw [this, map_zero]
  · rw [trOn, dite_eq_right hz]

/-- The traces of `f ∘ e` on `A` and of `e ∘ f` on `B` agree when `e` maps `A` to `B` and `f`
maps `B` to `A`. -/
theorem trOn_mul_comm {A B : Submodule k U} {e f : Module.End k U} (he : ∀ v ∈ A, e v ∈ B)
    (hf : ∀ v ∈ B, f v ∈ A) : trOn A (f * e) = trOn B (e * f) := by
  have hfe : ∀ v ∈ A, (f * e) v ∈ A := fun v hv => hf _ (he v hv)
  have hef : ∀ v ∈ B, (e * f) v ∈ B := fun v hv => he _ (hf v hv)
  rw [trOn_eq hfe, trOn_eq hef]
  have h1 : (f * e).restrict hfe = (f.restrict hf) ∘ₗ (e.restrict he) :=
    LinearMap.ext fun v => Subtype.ext rfl
  have h2 : (e * f).restrict hef = (e.restrict he) ∘ₗ (f.restrict hf) :=
    LinearMap.ext fun v => Subtype.ext rfl
  rw [h1, h2, LinearMap.trace_comp_comm']

end TraceOn

section Core

variable {k : Type*} [Field k] [CharZero k] {U : Type*} [AddCommGroup U] [Module k U]
  [FiniteDimensional k U] {X : Type*} [AddCommGroup X] [IsAddTorsionFree X]
  {Y : Type*} [AddCommGroup Y] {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Type*}
  [Fintype J] [DecidableEq J]
  {P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ} (yb : Basis ι ℤ Y) {W : X → Submodule k U}
  {g : LieSubalgebra k (Module.End k U)} {root : J → X} {V : Submodule k U}

omit [CharZero k] [FiniteDimensional k U] [IsAddTorsionFree X] in
theorem mem_inf_of_mem (hV : ∀ x ∈ g, ∀ v ∈ V, x v ∈ V) {χ : X} {x : Module.End k U}
    (hx : x ∈ g.toSubmodule ⊓ shift W χ) {μ ν : X} (hμν : μ + χ = ν) {v : U}
    (hv : v ∈ V ⊓ W μ) : x v ∈ V ⊓ W ν :=
  Submodule.mem_inf.mpr ⟨hV x (Submodule.mem_inf.mp hx).1 v (Submodule.mem_inf.mp hv).1,
    mapsTo_of_mem_shift (Submodule.mem_inf.mp hx).2 hμν (Submodule.mem_inf.mp hv).2⟩

namespace Hyp

variable (h : Hyp P W g root)
include h

omit [Fintype J] [DecidableEq J] in
/-- The commutator `[e_i, f_i]` acts on `W μ` by `F(μ, α_i)`. -/
theorem commutator_e_f_apply (i : J) (μ : X) {u : U} (hu : u ∈ W μ) :
    (h.e yb i * h.f yb i - h.f yb i * h.e yb i) u =
      ((GramDual.form P yb (mult W) μ (root i) : ℚ) : k) • u := by
  have he := Submodule.mem_inf.mp (h.e_mem yb i)
  have hf := Submodule.mem_inf.mp (h.f_mem yb i)
  have hmem : h.e yb i * h.f yb i - h.f yb i * h.e yb i ∈ g.toSubmodule ⊓ shift W 0 := by
    refine Submodule.mem_inf.mpr ⟨g.lie_mem he.1 hf.1, ?_⟩
    have := commutator_mem_shift he.2 hf.2
    rwa [add_neg_cancel] at this
  obtain ⟨a, ha⟩ := h.exists_eq_τ yb hmem
  have hMa : Mk P yb W *ᵥ a = ck k P yb (root i) := by
    funext l
    rw [← h.trace_t_mul_τ yb l a, ← ha]
    have hcomm := (h.isScalarOn_t yb l).commutator
      (fun μ ν => by simp only [ck, map_add, LinearMap.add_apply, Int.cast_add])
      h.iSup_eq_top he.2
    have key : h.t yb l * (h.e yb i * h.f yb i - h.f yb i * h.e yb i) =
        (h.t yb l * h.e yb i - h.e yb i * h.t yb l) * h.f yb i +
          (h.e yb i * (h.t yb l * h.f yb i) - (h.t yb l * h.f yb i) * h.e yb i) := by
      noncomm_ring
    rw [key, map_add, map_sub (LinearMap.trace k U), LinearMap.trace_mul_comm k (h.e yb i),
      sub_self, add_zero, hcomm, smul_mul_assoc, map_smul, h.trace_e_mul_f yb i, smul_eq_mul,
      mul_one]
  have ha' := h.τ_eq_of_Mk_mulVec yb hMa
  rw [ha, h.isScalarOn_τ yb a μ u hu, ha']
  dsimp only
  rw [dotProduct_comm, ← Hyp.form_cast (W := W) yb]

omit [CharZero k] [FiniteDimensional k U] [IsAddTorsionFree X] [DecidableEq J] in
/-- `∑_i F(μ, α_i) = 0`, since the roots are closed under negation. -/
theorem sum_form_root_eq_zero (μ : X) :
    ∑ i, GramDual.form P yb (mult W) μ (root i) = 0 := by
  choose σ hσ using h.exists_neg
  have hinj : Injective σ := fun i i' hii =>
    h.root_injective (neg_injective (by rw [← hσ, ← hσ, hii]))
  let e := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  have hS := Equiv.sum_comp e fun i => GramDual.form P yb (mult W) μ (root i)
  simp only [e, Equiv.ofBijective_apply, hσ, map_neg, Finset.sum_neg_distrib] at hS
  linarith

omit [FiniteDimensional k U] [IsAddTorsionFree X] [Fintype J] [DecidableEq J] in
/-- The torus part of the Casimir element acts on `W μ` by `F(μ, μ)`. -/
theorem sum_t_mul_td_apply (μ : X) {u : U} (hu : u ∈ W μ) :
    (∑ j, h.t yb j * h.td yb j) u = ((GramDual.form P yb (mult W) μ μ : ℚ) : k) • u := by
  rw [Hyp.form_cast (W := W) yb, LinearMap.sum_apply, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.End.mul_apply, td, h.isScalarOn_τ yb _ μ u hu, map_smul, h.isScalarOn_t yb j μ u hu,
    smul_smul, mul_comm]
  rfl

variable (hV : ∀ x ∈ g, ∀ v ∈ V, x v ∈ V)
include hV

omit [Fintype J] [DecidableEq J] in
/-- One step of Freudenthal's recursion for the traces of `e_i f_i`. -/
theorem trOn_e_mul_f (i : J) (μ : X) :
    trOn (V ⊓ W μ) (h.e yb i * h.f yb i) =
      trOn (V ⊓ W (μ + root i)) (h.e yb i * h.f yb i) +
        ((GramDual.form P yb (mult W) μ (root i) : ℚ) : k) * finrank k ↥(V ⊓ W μ) := by
  have he : ∀ v ∈ V ⊓ W μ, h.e yb i v ∈ V ⊓ W (μ + root i) :=
    fun v hv => mem_inf_of_mem hV (h.e_mem yb i) rfl hv
  have hf : ∀ v ∈ V ⊓ W (μ + root i), h.f yb i v ∈ V ⊓ W μ :=
    fun v hv => mem_inf_of_mem hV (h.f_mem yb i) (add_neg_cancel_right μ (root i)) hv
  have hfe : ∀ v ∈ V ⊓ W μ, (h.f yb i * h.e yb i) v ∈ V ⊓ W μ := fun v hv => hf _ (he v hv)
  have hsc : ∀ v ∈ V ⊓ W μ, (h.e yb i * h.f yb i - h.f yb i * h.e yb i) v =
      ((GramDual.form P yb (mult W) μ (root i) : ℚ) : k) • v :=
    fun v hv => h.commutator_e_f_apply yb i μ (Submodule.mem_inf.mp hv).2
  have hsc' : ∀ v ∈ V ⊓ W μ, (h.e yb i * h.f yb i - h.f yb i * h.e yb i) v ∈ V ⊓ W μ :=
    fun v hv => by rw [hsc v hv]; exact Submodule.smul_mem _ _ hv
  have hsplit : h.e yb i * h.f yb i =
      h.f yb i * h.e yb i + (h.e yb i * h.f yb i - h.f yb i * h.e yb i) := by abel
  conv_lhs => rw [hsplit]
  rw [trOn_add hfe hsc', trOn_eq_mul_finrank hsc, trOn_mul_comm he hf]

omit [Fintype J] [DecidableEq J] in
/-- Iterating the recursion along the `α_i`-string. -/
theorem trOn_e_mul_f_eq_sum (i : J) (μ : X) (d : ℕ) :
    trOn (V ⊓ W μ) (h.e yb i * h.f yb i) =
      ∑ j ∈ Finset.range d, ((GramDual.form P yb (mult W) (μ + j • root i) (root i) : ℚ) : k) *
          finrank k ↥(V ⊓ W (μ + j • root i)) +
        trOn (V ⊓ W (μ + d • root i)) (h.e yb i * h.f yb i) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : μ + (d + 1) • root i = μ + d • root i + root i := by
      rw [succ_nsmul, add_assoc]
    rw [ih, h.trOn_e_mul_f yb hV i (μ + d • root i), Finset.sum_range_succ, hd]
    ring

omit [Fintype J] [DecidableEq J] in
/-- The trace of `e_i f_i` on `V ⊓ W μ` as a sum along the `α_i`-string. -/
theorem trOn_e_mul_f_eq_finsum (i : J) (μ : X) :
    trOn (V ⊓ W μ) (h.e yb i * h.f yb i) =
      ((GramDual.form P yb (mult W) μ (root i) : ℚ) : k) * finrank k ↥(V ⊓ W μ) +
        ((∑ᶠ j : ℕ, GramDual.form P yb (mult W) (μ + (j + 1) • root i) (root i) *
          (finrank k ↥(V ⊓ W (μ + (j + 1) • root i)) : ℚ) : ℚ) : k) := by
  obtain ⟨N, hN⟩ := exists_forall_ge_eq_bot h.indep (h.root_ne_zero i) μ
  have hVN : ∀ j, N ≤ j → V ⊓ W (μ + j • root i) = ⊥ := fun j hj => by
    rw [hN j hj, inf_bot_eq]
  have hsupp : support (fun j : ℕ => GramDual.form P yb (mult W) (μ + (j + 1) • root i)
      (root i) * (finrank k ↥(V ⊓ W (μ + (j + 1) • root i)) : ℚ)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    dsimp only
    rw [hVN (j + 1) (by omega), finrank_bot, Nat.cast_zero, mul_zero]
  rw [h.trOn_e_mul_f_eq_sum yb hV i μ (N + 1), trOn_eq_zero_of_eq_bot (hVN _ (Nat.le_succ N)), add_zero, Finset.sum_range_succ', finsum_eq_sum_of_support_subset _ hsupp]
  push_cast
  simp only [zero_smul, add_zero]
  rw [zero_smul, add_zero]
  exact add_comm _ _

omit [DecidableEq J] in
/-- The trace of the Casimir element on `V ⊓ W μ`. -/
theorem trOn_casimir (μ : X) :
    trOn (V ⊓ W μ) (h.casimir yb) =
      ((GramDual.form P yb (mult W) μ μ : ℚ) : k) * finrank k ↥(V ⊓ W μ) +
        ∑ i, trOn (V ⊓ W μ) (h.e yb i * h.f yb i) := by
  have hT : ∀ v ∈ V ⊓ W μ, (∑ j, h.t yb j * h.td yb j) v =
      ((GramDual.form P yb (mult W) μ μ : ℚ) : k) • v :=
    fun v hv => h.sum_t_mul_td_apply yb μ (Submodule.mem_inf.mp hv).2
  have hT' : ∀ v ∈ V ⊓ W μ, (∑ j, h.t yb j * h.td yb j) v ∈ V ⊓ W μ :=
    fun v hv => by rw [hT v hv]; exact Submodule.smul_mem _ _ hv
  have hef : ∀ i ∈ Finset.univ, ∀ v ∈ V ⊓ W μ, (h.e yb i * h.f yb i) v ∈ V ⊓ W μ := by
    intro i _ v hv
    have h1 := mem_inf_of_mem hV (h.f_mem yb i) (sub_eq_add_neg μ (root i)).symm hv
    exact mem_inf_of_mem hV (h.e_mem yb i) (sub_add_cancel μ (root i)) h1
  have hE : ∀ v ∈ V ⊓ W μ, (∑ i, h.e yb i * h.f yb i) v ∈ V ⊓ W μ := by
    intro v hv
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i hi => hef i hi v hv
  rw [h.casimir_eq yb, trOn_add hT' hE, trOn_eq_mul_finrank hT, trOn_sum _ hef]

variable (hirr : ∀ K : Submodule k U, K ≤ V → (∀ x ∈ g, ∀ v ∈ K, x v ∈ K) → K ≠ ⊥ → K = V)
  {lam : X} (hlam : finrank k ↥(V ⊓ W lam) = 1)
include hirr hlam

omit [DecidableEq J] in
/-- The Casimir element acts on `V` by a scalar. -/
theorem exists_casimir_eq_smul : ∃ c : k, ∀ v ∈ V, h.casimir yb v = c • v := by
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp hlam
  have hΩ : h.casimir yb v₀ ∈ V ⊓ W lam := by
    refine Submodule.mem_inf.mpr
      ⟨h.casimir_mem_of_stable yb hV (Submodule.mem_inf.mp v₀.2).1, ?_⟩
    have := h.casimir_mem_shift yb lam _ (Submodule.mem_inf.mp v₀.2).2
    rwa [add_zero] at this
  obtain ⟨c, hc⟩ := hspan ⟨_, hΩ⟩
  have hc' : h.casimir yb v₀ = c • (v₀ : U) := (congrArg Subtype.val hc).symm
  refine ⟨c, ?_⟩
  have hmem : ∀ v, v ∈ LinearMap.ker (h.casimir yb - c • LinearMap.id) ↔
      h.casimir yb v = c • v := fun v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hK : V ⊓ LinearMap.ker (h.casimir yb - c • LinearMap.id) = V := by
    refine hirr _ inf_le_left (fun x hx v hv => ?_) ?_
    · obtain ⟨hvV, hvk⟩ := Submodule.mem_inf.mp hv
      refine Submodule.mem_inf.mpr ⟨hV x hx v hvV, ?_⟩
      rw [hmem] at hvk ⊢
      have hcomm := congrArg (fun F => F v) (h.commute_casimir yb hx).eq
      simp only [Module.End.mul_apply] at hcomm
      rw [← hcomm, hvk, map_smul]
    · intro hbot
      apply hv₀
      have h0 : (v₀ : U) ∈ V ⊓ LinearMap.ker (h.casimir yb - c • LinearMap.id) :=
        Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp v₀.2).1, (hmem _).mpr hc'⟩
      rw [hbot, Submodule.mem_bot] at h0
      exact Subtype.ext h0
  intro v hv
  rw [← hK] at hv
  exact (hmem v).mp (Submodule.mem_inf.mp hv).2

variable {pos : J → Prop} [DecidablePred pos]
  (hpos : ∀ i, pos i → V ⊓ W (lam + root i) = ⊥)
  (hneg : ∀ i, ¬pos i → V ⊓ W (lam - root i) = ⊥)
include hpos hneg

omit hirr [DecidableEq J] in
/-- The scalar by which the Casimir element acts on `V`, computed on `V ⊓ W lam`. -/
theorem casimir_scalar {c : k} (hc : ∀ v ∈ V, h.casimir yb v = c • v) :
    c = ((GramDual.form P yb (mult W) lam lam +
      ∑ i, if pos i then GramDual.form P yb (mult W) lam (root i) else 0 : ℚ) : k) := by
  have h1 := h.trOn_casimir yb hV lam
  rw [trOn_eq_mul_finrank fun v hv => hc v (Submodule.mem_inf.mp hv).1, hlam, Nat.cast_one,
    mul_one, mul_one] at h1
  rw [h1, Rat.cast_add, Rat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : pos i
  · rw [ite_eq_left hp, h.trOn_e_mul_f yb hV i lam, trOn_eq_zero_of_eq_bot (hpos i hp), hlam,
      Nat.cast_one, mul_one, zero_add]
  · rw [ite_eq_right hp, Rat.cast_zero]
    have hz : ∀ v ∈ V ⊓ W lam, (h.e yb i * h.f yb i) v = (0 : k) • v := by
      intro v hv
      have h2 := mem_inf_of_mem hV (h.f_mem yb i) (sub_eq_add_neg lam (root i)).symm hv
      rw [hneg i hp, Submodule.mem_bot] at h2
      rw [Module.End.mul_apply, h2, map_zero, zero_smul]
    rw [trOn_eq_mul_finrank hz, zero_mul]

omit [DecidableEq J] in
/-- Freudenthal's identity in `k`. -/
theorem freudenthal_cast (μ : X) :
    ((GramDual.form P yb (mult W) lam lam +
      ∑ i, (if pos i then GramDual.form P yb (mult W) lam (root i) else 0) -
        GramDual.form P yb (mult W) μ μ : ℚ) : k) * finrank k ↥(V ⊓ W μ) =
      ∑ i, ((∑ᶠ j : ℕ, GramDual.form P yb (mult W) (μ + (j + 1) • root i) (root i) *
        (finrank k ↥(V ⊓ W (μ + (j + 1) • root i)) : ℚ) : ℚ) : k) := by
  obtain ⟨c, hc⟩ := h.exists_casimir_eq_smul yb hV hirr hlam
  have hcs := h.casimir_scalar yb hV hlam hpos hneg hc
  have h1 := h.trOn_casimir yb hV μ
  rw [trOn_eq_mul_finrank fun v hv => hc v (Submodule.mem_inf.mp hv).1] at h1
  simp only [h.trOn_e_mul_f_eq_finsum yb hV _ μ] at h1
  have hz : ∑ i, ((GramDual.form P yb (mult W) μ (root i) : ℚ) : k) = 0 := by
    rw [← Rat.cast_sum, h.sum_form_root_eq_zero yb μ, Rat.cast_zero]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hz, zero_mul, zero_add] at h1
  rw [Rat.cast_sub, ← hcs]
  linear_combination h1

omit [DecidableEq J] in
/-- Freudenthal's identity in `ℚ`. -/
theorem freudenthal (μ : X) :
    (GramDual.form P yb (mult W) lam lam +
      ∑ i, (if pos i then GramDual.form P yb (mult W) lam (root i) else 0) -
        GramDual.form P yb (mult W) μ μ) * (finrank k ↥(V ⊓ W μ) : ℚ) =
      ∑ i, ∑ᶠ j : ℕ, GramDual.form P yb (mult W) (μ + (j + 1) • root i) (root i) *
        (finrank k ↥(V ⊓ W (μ + (j + 1) • root i)) : ℚ) := by
  have h1 := h.freudenthal_cast yb hV hirr hlam hpos hneg μ
  apply (Rat.cast_injective (α := k))
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum]
  exact h1

end Hyp

end Core

end Langlands.LinearAlgebra.FreudenthalCasimir

namespace Langlands.LinearAlgebra

open FreudenthalCasimir

/-- Proof of `FreudenthalCasimirCoreStatement`. -/
theorem freudenthalCasimirCoreStatement : FreudenthalCasimirCoreStatement := by
  intro k _ _ U _ _ _ X _ _ Y _ ι _ _ J _ P yb W g root V lam pos hindep htop hle htor hzero
    hbot hroot hfaith hne hinj hneg' hnil hV hirr hlam hpos hneg μ
  classical
  have : Fintype J := Fintype.ofFinite J
  have h : Hyp P W g root :=
    ⟨hindep, htop, hle, htor, hzero, hbot, hroot, hfaith, hne, hinj, hneg', hnil⟩
  have key := h.freudenthal yb hV hirr hlam hpos hneg μ
  simp only [finsum_eq_if]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact key

end Langlands.LinearAlgebra
