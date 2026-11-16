import Langlands.Representation.Archimedean.LowerVermaPBW
import Langlands.Representation.Archimedean.BGChaseReps

/-!
# Weights, central characters and filtrations for representations of `𝔤𝔩_n(ℂ)`

Generic tools for the lower Verma inputs of the Bernstein–Gelfand argument. See the paired
Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping

/-! ## Weights and invariant subspaces of a representation -/

section Rep

variable (n : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The weight `ε_p - ε_q` of the matrix unit `E_{(p,q)}`. -/
def rootOf (c : Idx n) : Fin n → ℂ := Pi.single c.1 1 - Pi.single c.2 1

/-- The total weight of the letters of a list. -/
def shiftOf (l : List (Idx n)) : Fin n → ℂ := (l.map (rootOf n)).sum

theorem shiftOf_cons (c : Idx n) (l : List (Idx n)) :
    shiftOf n (c :: l) = rootOf n c + shiftOf n l := by
  rw [shiftOf, List.map_cons, List.sum_cons, shiftOf]

/-- `v` is a weight vector of weight `μ`: `E_pp v = μ_p v` for all `p`. -/
def IsWt (v : V) (μ : Fin n → ℂ) : Prop := ∀ p, ρ (unitE n (p, p)) v = μ p • v

theorem env_W (l : List (Idx n)) :
    envelopingAction ρ (W n l) = (l.map fun c => ρ (unitE n c)).prod := by
  induction l with
  | nil => rw [W_nil, map_one, List.map_nil, List.prod_nil]
  | cons c l ih =>
    rw [W_cons, map_mul, ih, UniversalEnvelopingAlgebra.lift_ι_apply, List.map_cons,
      List.prod_cons]

theorem env_W_cons (c : Idx n) (l : List (Idx n)) (v : V) :
    envelopingAction ρ (W n (c :: l)) v = ρ (unitE n c) (envelopingAction ρ (W n l) v) := by
  rw [env_W, env_W, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem unitE_diag_eq (p : Fin n) : unitE n (p, p) = Matrix.diagonal (Pi.single p 1) := by
  ext i j
  simp only [unitE, Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h
    by_cases h' : p = i
    · subst h'; simp
    · simp [h', Ne.symm h']
  · simp [h]
    intro h1 h2
    exact h (h1.symm.trans h2)

theorem lie_unitE_diag (p : Fin n) (c : Idx n) :
    ⁅unitE n (p, p), unitE n c⁆ = rootOf n c p • unitE n c := by
  rw [unitE_diag_eq, lie_diagonal_unitE, rootOf]
  congr 1
  rw [Pi.sub_apply, Pi.single_comm p (1 : ℂ) c.1, Pi.single_comm p (1 : ℂ) c.2]

theorem isWt_unitE {v : V} {μ : Fin n → ℂ} (hv : IsWt n ρ v μ) (c : Idx n) :
    IsWt n ρ (ρ (unitE n c) v) (μ + rootOf n c) := by
  intro p
  have h := LieHom.map_lie ρ (unitE n (p, p)) (unitE n c)
  rw [lie_unitE_diag, map_smul, Ring.lie_def] at h
  have h2 := congrArg (fun T : Module.End ℂ V => T v) h
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, hv p,
    map_smul] at h2
  rw [eq_sub_iff_add_eq] at h2
  rw [← h2, Pi.add_apply, add_smul, add_comm]

theorem isWt_env_W {v : V} {μ : Fin n → ℂ} (hv : IsWt n ρ v μ) (l : List (Idx n)) :
    IsWt n ρ (envelopingAction ρ (W n l) v) (μ + shiftOf n l) := by
  induction l with
  | nil =>
    rw [W_nil, map_one, Module.End.one_apply, shiftOf, List.map_nil, List.sum_nil, add_zero]
    exact hv
  | cons c l ih =>
    rw [env_W_cons, shiftOf_cons]
    have := isWt_unitE n ρ ih c
    rwa [show μ + shiftOf n l + rootOf n c = μ + (rootOf n c + shiftOf n l) by abel] at this

theorem isWt_unique {v : V} {μ μ' : Fin n → ℂ} (h : IsWt n ρ v μ) (h' : IsWt n ρ v μ')
    (hv : v ≠ 0) : μ = μ' := by
  funext p
  have := (h p).symm.trans (h' p)
  exact smul_left_injective ℂ hv this

/-- `F` is stable under the matrix units. -/
def IsInv (F : Submodule ℂ V) : Prop := ∀ c : Idx n, ∀ x ∈ F, ρ (unitE n c) x ∈ F

theorem env_W_mem {F : Submodule ℂ V} (hF : IsInv n ρ F) (l : List (Idx n)) {x : V}
    (hx : x ∈ F) : envelopingAction ρ (W n l) x ∈ F := by
  induction l with
  | nil => rw [W_nil, map_one, Module.End.one_apply]; exact hx
  | cons c l ih => rw [env_W_cons]; exact hF c _ ih

theorem env_mem {F : Submodule ℂ V} (hF : IsInv n ρ F) (u : VermaGL.glU n) {x : V}
    (hx : x ∈ F) : envelopingAction ρ u x ∈ F := by
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply]
    exact env_W_mem n ρ hF _ hx
  | zero => rw [map_zero, LinearMap.zero_apply]; exact F.zero_mem
  | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply]; exact F.add_mem hu hv
  | smul a u _ hu => rw [map_smul, LinearMap.smul_apply]; exact F.smul_mem a hu

/-- A vector that is singular of weight `μ` modulo an invariant subspace `F` is mapped into
`F` by the defining ideal of `M⁻(μ)`. -/
theorem env_ideal_mem {F : Submodule ℂ V} (hF : IsInv n ρ F) (μ : Fin n → ℂ) (G : V)
    (hlow : ∀ p q : Fin n, q < p → ρ (unitE n (p, q)) G ∈ F)
    (hdiag : ∀ p, ρ (unitE n (p, p)) G - μ p • G ∈ F) {u : VermaGL.glU n}
    (hu : u ∈ VermaGL.lowerVermaIdeal n μ) : envelopingAction ρ u G ∈ F := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, q, hqp, rfl⟩ | ⟨p, rfl⟩
    · rw [VermaGL.unitU, UniversalEnvelopingAlgebra.lift_ι_apply]
      exact hlow p q hqp
    · rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply,
        VermaGL.unitU, UniversalEnvelopingAlgebra.lift_ι_apply]
      exact hdiag p
  | zero => rw [map_zero, LinearMap.zero_apply]; exact F.zero_mem
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact F.add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, map_mul, Module.End.mul_apply]; exact env_mem n ρ hF a hx

theorem isInv_bot : IsInv n ρ ⊥ := by
  intro c x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/-- Separation of eigenvalues for one operator. -/
theorem mem_span_eigen {T : Module.End ℂ V} {s : Set V} (hs : ∀ v ∈ s, ∃ a : ℂ, T v = a • v)
    {x : V} (hx : x ∈ Submodule.span ℂ s) {c : ℂ} (hxc : T x = c • x) :
    x ∈ Submodule.span ℂ {v | v ∈ s ∧ T v = c • v} := by
  set A := Submodule.span ℂ {v | v ∈ s ∧ T v = c • v}
  set N := ⨆ (a : ℂ) (_ : a ≠ c), Module.End.eigenspace T a
  have hA : A ≤ Module.End.eigenspace T c := by
    refine Submodule.span_le.mpr fun v hv => ?_
    exact Module.End.mem_eigenspace_iff.mpr hv.2
  have hle : Submodule.span ℂ s ≤ A ⊔ N := by
    refine Submodule.span_le.mpr fun v hv => ?_
    obtain ⟨a, ha⟩ := hs v hv
    by_cases hac : a = c
    · subst hac
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨hv, ha⟩)
    · refine Submodule.mem_sup_right ?_
      exact (le_iSup₂ (f := fun (a : ℂ) (_ : a ≠ c) => Module.End.eigenspace T a) a hac)
        (Module.End.mem_eigenspace_iff.mpr ha)
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp (hle hx)
  have hTy : T y = c • y := Module.End.mem_eigenspace_iff.mp (hA hy)
  have hTw : T w = c • w := by
    have : T w = T (y + w) - T y := by rw [map_add]; abel
    rw [this, hxc, hTy, smul_add]
    abel
  have hdisj := (iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep T)) c
  have hw0 : w = 0 :=
    (Submodule.disjoint_def.mp hdisj) w (Module.End.mem_eigenspace_iff.mpr hTw) hw
  rw [hw0, add_zero]
  exact hy

/-- Separation of joint weights. -/
theorem mem_span_wt {s : Set V} (hs : ∀ v ∈ s, ∃ μ, IsWt n ρ v μ) {x : V}
    (hx : x ∈ Submodule.span ℂ s) {μ₀ : Fin n → ℂ} (hxw : IsWt n ρ x μ₀) :
    x ∈ Submodule.span ℂ {v | v ∈ s ∧ IsWt n ρ v μ₀} := by
  have key : ∀ P : Finset (Fin n), x ∈ Submodule.span ℂ
      {v | v ∈ s ∧ ∀ p ∈ P, ρ (unitE n (p, p)) v = μ₀ p • v} := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      have hsub : s ⊆ {v | v ∈ s ∧ ∀ p ∈ (∅ : Finset (Fin n)),
          ρ (unitE n (p, p)) v = μ₀ p • v} :=
        fun v hv => ⟨hv, fun p hp => absurd hp (Finset.notMem_empty p)⟩
      exact Submodule.span_mono hsub hx
    | insert p P hp ih =>
      have h := mem_span_eigen (T := ρ (unitE n (p, p)))
        (s := {v | v ∈ s ∧ ∀ p ∈ P, ρ (unitE n (p, p)) v = μ₀ p • v})
        (fun v hv => by
          obtain ⟨μ, hμ⟩ := hs v hv.1
          exact ⟨μ p, hμ p⟩) ih (hxw p)
      have hsub : {v | v ∈ {v | v ∈ s ∧ ∀ p ∈ P, ρ (unitE n (p, p)) v = μ₀ p • v} ∧
          ρ (unitE n (p, p)) v = μ₀ p • v} ⊆
          {v | v ∈ s ∧ ∀ r ∈ insert p P, ρ (unitE n (r, r)) v = μ₀ r • v} := by
        rintro v ⟨⟨hv1, hv2⟩, hv3⟩
        refine ⟨hv1, fun r hr => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hv3
        · exact hv2 r hr
      exact Submodule.span_mono hsub h
  have hsub : {v | v ∈ s ∧ ∀ p ∈ (Finset.univ : Finset (Fin n)),
      ρ (unitE n (p, p)) v = μ₀ p • v} ⊆ {v | v ∈ s ∧ IsWt n ρ v μ₀} :=
    fun v hv => ⟨hv.1, fun p => hv.2 p (Finset.mem_univ p)⟩
  exact Submodule.span_mono hsub (key Finset.univ)

end Rep

/-! ## Central characters of lower Verma modules -/

section Central

variable (n : ℕ)

theorem center_smul_gen (μ : Fin n → ℂ) {z : VermaGL.glU n} (hz : z ∈ VermaGL.center n) :
    ∃ c : ℂ, z • VermaGL.gen n μ = c • VermaGL.gen n μ := by
  have hcomm : ∀ u : VermaGL.glU n, u * z = z * u := fun u =>
    Subalgebra.mem_center_iff.mp hz u
  exact (lowerVermaWeight n μ).2 _ (fun p => by
    rw [smul_smul, hcomm, mul_smul, unitU_smul_gen, smul_comm])

theorem sub_mem_lowerVermaIdeal (μ : Fin n → ℂ) {z : VermaGL.glU n} {c : ℂ}
    (h : z • VermaGL.gen n μ = c • VermaGL.gen n μ) :
    z - algebraMap ℂ (VermaGL.glU n) c ∈ VermaGL.lowerVermaIdeal n μ := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  rw [Submodule.Quotient.mk_sub, mk_eq_smul_gen, mk_eq_smul_gen, h, algebraMap_smul, sub_self]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- If `G` is singular of weight `μ` modulo `F` and `z • gen μ = c • gen μ`, then
`z G - c G ∈ F`. -/
theorem env_center_sub_mem {F : Submodule ℂ V} (hF : IsInv n ρ F) (μ : Fin n → ℂ) (G : V)
    (hlow : ∀ p q : Fin n, q < p → ρ (unitE n (p, q)) G ∈ F)
    (hdiag : ∀ p, ρ (unitE n (p, p)) G - μ p • G ∈ F) {z : VermaGL.glU n} {c : ℂ}
    (h : z • VermaGL.gen n μ = c • VermaGL.gen n μ) :
    envelopingAction ρ z G - c • G ∈ F := by
  have h' := env_ideal_mem n ρ hF μ G hlow hdiag (sub_mem_lowerVermaIdeal n μ h)
  rwa [map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply] at h'

end Central

/-! ## Weight bases of finite-dimensional representations -/

section WeightBasis

variable (n : ℕ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)

/-- `W` has a basis of weight vectors with integral weights, indexed by `Fin D`
(from the Library's `BGChase.exists_wtBasis`). -/
theorem exists_weight_basis [FiniteDimensional ℂ Wt] (hσ : VermaGL.HasIntegralWeights σ) :
    ∃ (D : ℕ) (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ),
      ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k := by
  obtain ⟨ι, _, b, μ, hb⟩ := BGChase.exists_wtBasis (H := BGChase.diagOps σ) hσ
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card ι, b.reindex e, fun k => μ (e.symm k), fun k p => by
    rw [Module.Basis.reindex_apply]
    exact hb (e.symm k) p⟩

variable {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)

/-- The weight of `b k` as a complex vector. -/
def wtC (k : Fin D) : Fin n → ℂ := fun p => (m k p : ℂ)

/-- The height `Σ_p (-p) m_p` of the weight of `b k`. -/
def htZ (k : Fin D) : ℤ := ∑ p : Fin n, (-((p : ℕ) : ℤ)) * m k p

theorem htZ_cast (k : Fin D) : (htZ n m k : ℂ) = ∑ p : Fin n, dZero n p * wtC n m k p := by
  simp [htZ, dZero, wtC]

theorem sum_dZero_rootOf (c : Idx n) :
    ∑ p : Fin n, dZero n p * rootOf n c p = dZero n c.1 - dZero n c.2 := by
  simp [rootOf, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem sum_dZero_shiftOf (l : List (Idx n)) :
    ∑ p : Fin n, dZero n p * shiftOf n l p = (l.map fun c => dZero n c.1 - dZero n c.2).sum := by
  induction l with
  | nil => simp [shiftOf]
  | cons c l ih =>
    rw [shiftOf_cons, List.map_cons, List.sum_cons, ← ih, ← sum_dZero_rootOf,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.add_apply, mul_add]

theorem eq_nil_of_shiftOf_eq_zero {l : List (Idx n)} (hl : ∀ c ∈ l, c.1 < c.2)
    (h0 : shiftOf n l = 0) : l = [] := by
  by_contra hne
  apply sum_shift_ne_zero n l hl hne
  rw [← sum_dZero_shiftOf, h0]
  simp

theorem htZ_lt_of_wtC_eq {k i : Fin D} {p q : Fin n} (hqp : q < p)
    (h : wtC n m k = wtC n m i + rootOf n (p, q)) : htZ n m k < htZ n m i := by
  have hc : (htZ n m k : ℂ) = (htZ n m i : ℂ) + (((q : ℕ) : ℤ) - ((p : ℕ) : ℤ) : ℤ) := by
    rw [htZ_cast, htZ_cast, h]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [sum_dZero_rootOf]
    simp [dZero]
    ring
  have hz : htZ n m k = htZ n m i + (((q : ℕ) : ℤ) - ((p : ℕ) : ℤ)) := by exact_mod_cast hc
  have : (q : ℕ) < (p : ℕ) := hqp
  omega

variable (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

include hb in
theorem coord_unitE_diag (k : Fin D) (p : Fin n) (w : Wt) :
    b.coord k (σ (unitE n (p, p)) w) = (m k p : ℂ) * b.coord k w :=
  LinearMap.congr_fun (BGChase.coord_comp_of_isWt b (H := BGChase.diagOps σ) hb k p) w

include hb in
theorem isWt_b (k : Fin D) : IsWt n σ (b k) (wtC n m k) := hb k

include hb in
theorem wtC_eq_of_coord_ne_zero {v : Wt} {μ : Fin n → ℂ} (hv : IsWt n σ v μ) {k : Fin D}
    (hk : b.coord k v ≠ 0) : wtC n m k = μ := by
  funext p
  have h1 := congrArg (b.coord k) (hv p)
  rw [coord_unitE_diag n σ b m hb, map_smul, smul_eq_mul] at h1
  exact mul_right_cancel₀ hk h1

include hb in
theorem wtC_eq_of_lower_coeff {k i : Fin D} (c : Idx n)
    (h : b.coord k (σ (unitE n c) (b i)) ≠ 0) : wtC n m k = wtC n m i + rootOf n c :=
  wtC_eq_of_coord_ne_zero n σ b m hb (isWt_unitE n σ (isWt_b n σ b m hb i) c) h

theorem isInv_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) {s : Set V}
    (hs : ∀ c : Idx n, ∀ v ∈ s, ρ (unitE n c) v ∈ Submodule.span ℂ s) :
    IsInv n ρ (Submodule.span ℂ s) := by
  intro c x hx
  induction hx using Submodule.span_induction with
  | mem v hv => exact hs c v hv
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem shiftOf_mem_posRootCone {l : List (Idx n)} (hl : ∀ c ∈ l, c.1 < c.2) :
    shiftOf n l ∈ VermaGL.posRootCone n := by
  refine (VermaGL.posRootCone n).list_sum_mem fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact AddSubmonoid.subset_closure ⟨c.1, c.2, hl c hc, rfl⟩


end WeightBasis

/-! ## The cone `Q₊` -/

section Cone

variable (n : ℕ)

theorem exists_shiftOf_of_mem_posRootCone {β : Fin n → ℂ} (hβ : β ∈ VermaGL.posRootCone n) :
    ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧ β = shiftOf n l := by
  induction hβ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    obtain ⟨p, q, hpq, rfl⟩ := hβ
    exact ⟨[(p, q)], by simpa using hpq, by simp [shiftOf, rootOf]⟩
  | zero => exact ⟨[], by simp, by simp [shiftOf]⟩
  | add β γ _ _ hβ hγ =>
    obtain ⟨l, hl, rfl⟩ := hβ
    obtain ⟨l', hl', rfl⟩ := hγ
    refine ⟨l ++ l', fun c hc => ?_, by simp [shiftOf, List.map_append, List.sum_append]⟩
    rcases List.mem_append.mp hc with h | h
    · exact hl c h
    · exact hl' c h

theorem posRootCone_antisymm {β : Fin n → ℂ} (h1 : β ∈ VermaGL.posRootCone n)
    (h2 : -β ∈ VermaGL.posRootCone n) : β = 0 := by
  obtain ⟨l, hl, rfl⟩ := exists_shiftOf_of_mem_posRootCone n h1
  obtain ⟨l', hl', hl'eq⟩ := exists_shiftOf_of_mem_posRootCone n h2
  have h0 : shiftOf n (l ++ l') = 0 := by
    rw [shiftOf, List.map_append, List.sum_append, ← shiftOf, ← shiftOf, ← hl'eq]
    abel
  have hnil := eq_nil_of_shiftOf_eq_zero n (l := l ++ l') (fun c hc => by
    rcases List.mem_append.mp hc with h | h
    · exact hl c h
    · exact hl' c h) h0
  rw [List.append_eq_nil_iff] at hnil
  rw [hnil.1]
  simp [shiftOf]

end Cone

/-! ## Filtrations generated by weight vectors -/

section FiltrationG

variable (n : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) {ι : Type*} (G : ι → V)

/-- The vectors `E_{c₁} ⋯ E_{c_r} · G j`, `j ∈ T`. -/
def gensG (T : Finset ι) : Set V :=
  {v | ∃ j ∈ T, ∃ l : List (Idx n), v = envelopingAction ρ (W n l) (G j)}

/-- The invariant subspace generated by the `G j`, `j ∈ T`. -/
def FG (T : Finset ι) : Submodule ℂ V := Submodule.span ℂ (gensG n ρ G T)

theorem isInv_FG (T : Finset ι) : IsInv n ρ (FG n ρ G T) := by
  refine isInv_span n _ fun c v hv => ?_
  obtain ⟨j, hj, l, rfl⟩ := hv
  refine Submodule.subset_span ⟨j, hj, c :: l, ?_⟩
  rw [env_W_cons]

theorem FG_mono {T T' : Finset ι} (h : T ⊆ T') : FG n ρ G T ≤ FG n ρ G T' := by
  refine Submodule.span_mono fun v hv => ?_
  obtain ⟨j, hj, l, rfl⟩ := hv
  exact ⟨j, h hj, l, rfl⟩

theorem G_mem_FG {T : Finset ι} {j : ι} (hj : j ∈ T) : G j ∈ FG n ρ G T :=
  Submodule.subset_span ⟨j, hj, [], by rw [W_nil, map_one, Module.End.one_apply]⟩

theorem FG_empty : FG n ρ G ∅ = ⊥ := by
  rw [FG, Submodule.span_eq_bot]
  rintro v ⟨j, hj, -⟩
  exact absurd hj (Finset.notMem_empty j)

/-- The upper words applied to `G k`. -/
def PG (k : ι) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧
    v = envelopingAction ρ (W n l) (G k)}

variable (μ : ι → Fin n → ℂ) (hG : ∀ j, IsWt n ρ (G j) (μ j))

include hG in
theorem isWt_gensG {T : Finset ι} {v : V} (hv : v ∈ gensG n ρ G T) :
    ∃ μ', IsWt n ρ v μ' := by
  obtain ⟨j, -, l, rfl⟩ := hv
  exact ⟨_, isWt_env_W n ρ (hG j) l⟩

variable [DecidableEq ι] {T : Finset ι} {k : ι}
  (hlow : ∀ p q : Fin n, q < p → ρ (unitE n (p, q)) (G k) ∈ FG n ρ G (T.erase k))

include hG hlow in
theorem envG_lower_mem (l : List (Idx n)) (hl : ∀ c ∈ l, ¬ c.1 < c.2) :
    envelopingAction ρ (W n l) (G k) ∈ FG n ρ G (T.erase k) ⊔ ℂ ∙ G k := by
  induction l with
  | nil =>
    rw [W_nil, map_one, Module.End.one_apply]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cons c l ih =>
    rw [env_W_cons]
    obtain ⟨f, hf, y, hy, hfy⟩ := Submodule.mem_sup.mp
      (ih fun d hd => hl d (List.mem_cons_of_mem c hd))
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [← hfy, map_add, map_smul]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (isInv_FG n ρ G _ c f hf)) ?_
    have hc := hl c List.mem_cons_self
    rcases lt_or_eq_of_le (not_lt.mp hc) with h | h
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ a (hlow _ _ h))
    · obtain ⟨c1, c2⟩ := c
      dsimp only at h
      subst h
      rw [hG k c2, smul_smul]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

include hG hlow in
theorem envG_mem_sup (u : VermaGL.glU n) :
    envelopingAction ρ u (G k) ∈ FG n ρ G (T.erase k) ⊔ PG n ρ G k := by
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply_split, map_mul, Module.End.mul_apply]
    have hlw := envG_lower_mem n ρ G μ hG hlow (Kostant.expand ((loList n).map Subtype.val) α)
      (fun c hc => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp (mem_expand hc)
        exact c'.2)
    obtain ⟨f, hf, y, hy, hfy⟩ := Submodule.mem_sup.mp hlw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [← hfy, map_add, map_smul]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (env_W_mem n _ (isInv_FG n ρ G _) _ hf))
      (Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.subset_span ⟨_, ?_, rfl⟩)))
    intro c hc
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp (mem_expand hc)
    exact c'.2
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ a hx

include hG hlow in
theorem FG_le_sup : FG n ρ G T ≤ FG n ρ G (T.erase k) ⊔ PG n ρ G k := by
  refine Submodule.span_le.mpr fun v hv => ?_
  obtain ⟨j, hj, l, rfl⟩ := hv
  by_cases hjk : j = k
  · subst hjk
    exact envG_mem_sup n ρ G μ hG hlow _
  · exact Submodule.mem_sup_left
      (Submodule.subset_span ⟨j, Finset.mem_erase.mpr ⟨hjk, hj⟩, l, rfl⟩)

include hG hlow in
/-- **Weight separation.** A weight vector of weight `ν` in `F_T` lies in `F_{T∖k}` plus the
span of the upper words `w · G k` of weight `ν`. -/
theorem mem_FG_weight {x : V} (hx : x ∈ FG n ρ G T) {ν : Fin n → ℂ} (hxw : IsWt n ρ x ν) :
    x ∈ FG n ρ G (T.erase k) ⊔ Submodule.span ℂ {v | ∃ l : List (Idx n),
      (∀ c ∈ l, c.1 < c.2) ∧ μ k + shiftOf n l = ν ∧ v = envelopingAction ρ (W n l) (G k)} := by
  set s₂ : Set V := {v | ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧
    v = envelopingAction ρ (W n l) (G k)}
  have hx1 : x ∈ Submodule.span ℂ (gensG n ρ G (T.erase k) ∪ s₂) := by
    rw [Submodule.span_union]
    exact FG_le_sup n ρ G μ hG hlow hx
  have hx2 := mem_span_wt n ρ (fun v hv => by
      rcases hv with hv | ⟨l, -, rfl⟩
      · exact isWt_gensG n ρ G μ hG hv
      · exact ⟨_, isWt_env_W n ρ (hG k) l⟩) hx1 hxw
  refine (Submodule.span_le.mpr ?_) hx2
  rintro v ⟨hv | ⟨l, hl, rfl⟩, hvw⟩
  · exact Submodule.mem_sup_left (Submodule.subset_span hv)
  · by_cases h0 : envelopingAction ρ (W n l) (G k) = 0
    · rw [h0]
      exact Submodule.zero_mem _
    · have hu := isWt_unique n ρ (isWt_env_W n ρ (hG k) l) hvw h0
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨l, hl, hu, rfl⟩)

variable (hk : k ∈ T)

include hG hlow in
/-- `z` acts on `F_T / F_{T∖k}` by its scalar on `gen (μ k)`. -/
theorem FG_center_sub_mem {z : VermaGL.glU n} (hz : z ∈ VermaGL.center n) {d : ℂ}
    (hd : z • VermaGL.gen n (μ k) = d • VermaGL.gen n (μ k)) {x : V} (hx : x ∈ FG n ρ G T) :
    envelopingAction ρ z x - d • x ∈ FG n ρ G (T.erase k) := by
  have hGz : envelopingAction ρ z (G k) - d • G k ∈ FG n ρ G (T.erase k) :=
    env_center_sub_mem n ρ (isInv_FG n ρ G _) (μ k) (G k) hlow
      (fun p => by rw [hG k p, sub_self]; exact Submodule.zero_mem _) hd
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, hj, l, rfl⟩ := hv
    by_cases hjk : j = k
    · subst hjk
      rw [← Module.End.mul_apply, ← map_mul, ← Subalgebra.mem_center_iff.mp hz (W n l), map_mul,
        Module.End.mul_apply, ← map_smul, ← map_sub]
      exact env_W_mem n _ (isInv_FG n ρ G _) l hGz
    · have hv : envelopingAction ρ (W n l) (G j) ∈ FG n ρ G (T.erase k) :=
        Submodule.subset_span ⟨j, Finset.mem_erase.mpr ⟨hjk, hj⟩, l, rfl⟩
      exact Submodule.sub_mem _ (env_mem n _ (isInv_FG n ρ G _) z hv) (Submodule.smul_mem _ _ hv)
  | zero => rw [map_zero, smul_zero, sub_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h := Submodule.smul_mem _ a hx
    rw [smul_sub, smul_comm a d x, ← map_smul] at h
    exact h

include hG hlow in
theorem FG_center_pow_sub_mem {z : VermaGL.glU n} (hz : z ∈ VermaGL.center n) {d : ℂ}
    (hd : z • VermaGL.gen n (μ k) = d • VermaGL.gen n (μ k)) (c : ℂ) (N : ℕ) {x : V}
    (hx : x ∈ FG n ρ G T) :
    envelopingAction ρ ((z - algebraMap ℂ (VermaGL.glU n) c) ^ N) x - (d - c) ^ N • x ∈
      FG n ρ G (T.erase k) := by
  have hT : FG n ρ G (T.erase k) ≤ FG n ρ G T := FG_mono n ρ G (Finset.erase_subset k T)
  have h1 : ∀ y ∈ FG n ρ G T, envelopingAction ρ (z - algebraMap ℂ (VermaGL.glU n) c) y -
      (d - c) • y ∈ FG n ρ G (T.erase k) := by
    intro y hy
    have h := FG_center_sub_mem n ρ G μ hG hlow hz hd hy
    rwa [map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_smul,
      sub_sub_sub_cancel_right]
  induction N with
  | zero => rw [pow_zero, map_one, Module.End.one_apply, pow_zero, one_smul, sub_self]
            exact Submodule.zero_mem _
  | succ N ih =>
    obtain ⟨f, hf, hfeq⟩ : ∃ f ∈ FG n ρ G (T.erase k),
        envelopingAction ρ ((z - algebraMap ℂ (VermaGL.glU n) c) ^ N) x = (d - c) ^ N • x + f :=
      ⟨_, ih, by abel⟩
    rw [pow_succ', map_mul, Module.End.mul_apply, hfeq, map_add, map_smul]
    have h2 := Submodule.smul_mem _ ((d - c) ^ N) (h1 x hx)
    have h3 := env_mem n _ (isInv_FG n ρ G _) (z - algebraMap ℂ (VermaGL.glU n) c) hf
    have : (d - c) ^ N • envelopingAction ρ (z - algebraMap ℂ (VermaGL.glU n) c) x +
        envelopingAction ρ (z - algebraMap ℂ (VermaGL.glU n) c) f - (d - c) ^ (N + 1) • x =
        (d - c) ^ N • (envelopingAction ρ (z - algebraMap ℂ (VermaGL.glU n) c) x - (d - c) • x) +
          envelopingAction ρ (z - algebraMap ℂ (VermaGL.glU n) c) f := by
      rw [smul_sub, smul_smul, ← pow_succ]
      abel
    rw [this]
    exact Submodule.add_mem _ h2 h3

end FiltrationG

end Langlands.Archimedean.VermaPBW
