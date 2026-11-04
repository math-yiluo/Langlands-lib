import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Artinian.Module

/-! # Fitting decomposition of an admissible representation (proof of Corollary III.7.2)

For an admissible representation `(π, V)` and an intertwiner `T : V → V`, put
`V₁ = ⋂ₙ Tⁿ V` and `V₂ = ⋃ₙ Ker Tⁿ`. These are subrepresentations with `V = V₁ ⊕ V₂`, `T` is
bijective on `V₁`, and for every open subgroup `K` a single power of `T` kills `V₂ ∩ V^K`.
This is the linear-algebra core of Waldspurger's proof of Corollary III.7.2, where
`T = π(p)`.
-/

noncomputable section

universe u v

namespace Langlands.HarishChandraSchwartz

section Module

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Membership in `⋃ₙ Ker fⁿ`. -/
theorem mem_iSup_ker_pow {f : Module.End ℂ V} {v : V} :
    v ∈ ⨆ n : ℕ, LinearMap.ker (f ^ n) ↔ ∃ n : ℕ, (f ^ n) v = 0 := by
  have hd : Directed (· ≤ ·) fun n : ℕ => LinearMap.ker (f ^ n) :=
    f.iterateKer.monotone.directed_le
  exact (Submodule.mem_iSup_of_directed _ hd).trans (exists_congr fun _ => LinearMap.mem_ker)

end Module

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- The powers of an intertwiner are intertwiners. -/
theorem intertwiningMap_pow_apply (T : ρ.IntertwiningMap ρ) (n : ℕ) (g : G) (v : V) :
    (T.toLinearMap ^ n) (ρ g v) = ρ g ((T.toLinearMap ^ n) v) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply]
    exact T.isIntertwining ρ ρ g _

/-- On `K`-fixed vectors, the powers of the restriction `fixedVectorsMap T K` of `T` are the
restrictions of the powers of `T`. -/
theorem fixedVectorsMap_pow_apply (T : ρ.IntertwiningMap ρ) (K : Subgroup G) (n : ℕ)
    (y : fixedVectors ρ K) :
    (((fixedVectorsMap T K ^ n) y : fixedVectors ρ K) : V) = (T.toLinearMap ^ n) y := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    rfl

/-- Waldspurger's `V₁ = ⋂ₙ Tⁿ V` (proof of Corollary III.7.2, with `T = π(p)`), a
subrepresentation. -/
def fittingRange (T : ρ.IntertwiningMap ρ) : Subrepresentation ρ where
  toSubmodule := ⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ n)
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_iInf] at hv ⊢
    intro n
    obtain ⟨y, hy⟩ := hv n
    exact ⟨ρ g y, by rw [intertwiningMap_pow_apply, hy]⟩

theorem mem_fittingRange_iff {T : ρ.IntertwiningMap ρ} {v : V} :
    v ∈ fittingRange T ↔ ∀ n : ℕ, v ∈ LinearMap.range (T.toLinearMap ^ n) :=
  Submodule.mem_iInf _

/-- Waldspurger's `V₂ = ⋃ₙ Ker Tⁿ` (proof of Corollary III.7.2, with `T = π(p)`), a
subrepresentation. -/
def fittingKernel (T : ρ.IntertwiningMap ρ) : Subrepresentation ρ where
  toSubmodule := ⨆ n : ℕ, LinearMap.ker (T.toLinearMap ^ n)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨n, hn⟩ := mem_iSup_ker_pow.mp hv
    exact mem_iSup_ker_pow.mpr ⟨n, by rw [intertwiningMap_pow_apply, hn, map_zero]⟩

theorem mem_fittingKernel_iff {T : ρ.IntertwiningMap ρ} {v : V} :
    v ∈ fittingKernel T ↔ ∃ n : ℕ, (T.toLinearMap ^ n) v = 0 :=
  mem_iSup_ker_pow

/-- `T` maps `V₁` into itself. -/
theorem mapsTo_fittingRange (T : ρ.IntertwiningMap ρ) :
    Set.MapsTo T (fittingRange T) (fittingRange T) := by
  intro x hx
  rw [SetLike.mem_coe, mem_fittingRange_iff] at hx ⊢
  intro n
  obtain ⟨y, rfl⟩ := hx n
  refine ⟨T.toLinearMap y, ?_⟩
  rw [← Module.End.mul_apply, pow_mul_comm', Module.End.mul_apply]
  rfl

/-- `T` maps `V₂` into itself. -/
theorem mapsTo_fittingKernel (T : ρ.IntertwiningMap ρ) :
    Set.MapsTo T (fittingKernel T) (fittingKernel T) := by
  intro x hx
  rw [SetLike.mem_coe, mem_fittingKernel_iff] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  change (T.toLinearMap ^ n) (T.toLinearMap x) = 0
  rw [← Module.End.mul_apply, pow_mul_comm', Module.End.mul_apply, hn, map_zero]

variable [TopologicalSpace G]

/-- For an admissible `ρ` and an open subgroup `K`, a single power of `T` kills every vector of
`V₂` fixed by `K` (Waldspurger: `π₂(p)` is nilpotent). -/
theorem exists_pow_eq_zero_of_mem_fittingKernel (hρ : IsAdmissible ρ) (T : ρ.IntertwiningMap ρ)
    (K : OpenSubgroup G) :
    ∃ n : ℕ, ∀ v ∈ fittingKernel T, v ∈ fixedVectors ρ K.toSubgroup →
      (T.toLinearMap ^ n) v = 0 := by
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  obtain ⟨N, hN⟩ :=
    (LinearMap.eventually_iSup_ker_pow_eq (fixedVectorsMap T K.toSubgroup)).exists
  refine ⟨N, fun v hv hvK => ?_⟩
  obtain ⟨m, hm⟩ := mem_fittingKernel_iff.mp hv
  have hmem : (⟨v, hvK⟩ : fixedVectors ρ K.toSubgroup) ∈
      ⨆ n : ℕ, LinearMap.ker (fixedVectorsMap T K.toSubgroup ^ n) :=
    mem_iSup_ker_pow.mpr ⟨m, Subtype.ext (by rw [fixedVectorsMap_pow_apply]; exact hm)⟩
  rw [hN, LinearMap.mem_ker] at hmem
  have h := congrArg Subtype.val hmem
  rw [fixedVectorsMap_pow_apply] at h
  exact h

variable [IsTopologicalGroup G]

/-- If `x = Tⁿ y` is fixed by a compact open subgroup `K`, then `x = Tⁿ y'` with `y'` fixed by
`K`: the averaging projection onto `V^K` commutes with `T`. -/
theorem exists_fixed_preimage_pow (hρ : IsSmooth ρ) (T : ρ.IntertwiningMap ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {n : ℕ} {x : V}
    (hx : x ∈ fixedVectors ρ K.toSubgroup) (hxn : x ∈ LinearMap.range (T.toLinearMap ^ n)) :
    ∃ y ∈ fixedVectors ρ K.toSubgroup, (T.toLinearMap ^ n) y = x := by
  obtain ⟨y, rfl⟩ := hxn
  have hc : Commute T.toLinearMap (Compact.averageMap ρ hρ K hK) :=
    Compact.averageMap_commute ρ ρ hρ hρ K hK T
  refine ⟨Compact.averageMap ρ hρ K hK y, Compact.averageMap_mem_fixedVectors ρ hρ K hK y, ?_⟩
  rw [← Module.End.mul_apply, (hc.pow_left n).eq, Module.End.mul_apply,
    Compact.averageMap_id ρ hρ K hK _ hx]

omit [IsTopologicalGroup G] in
/-- Every vector of a smooth representation is fixed by a compact open subgroup, when every open
subgroup contains a compact open one. -/
theorem exists_isCompact_fixed (hρ : IsSmooth ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K) (x : V) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ x ∈ fixedVectors ρ K.toSubgroup := by
  obtain ⟨U, hU⟩ := hρ x
  obtain ⟨K, hK, hKU⟩ := hcof U
  exact ⟨K, hK, fixedVectors_antitone ρ (OpenSubgroup.toSubgroup_le.mpr hKU) hU⟩

/-- A `K`-fixed vector of `V₁` lies in `⋂ₙ Tⁿ V^K`, for `K` compact open. -/
theorem mem_iInf_range_fixedVectorsMap_pow (hρ : IsSmooth ρ) (T : ρ.IntertwiningMap ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {x : V} (hx₁ : x ∈ fittingRange T)
    (hx : x ∈ fixedVectors ρ K.toSubgroup) :
    (⟨x, hx⟩ : fixedVectors ρ K.toSubgroup) ∈
      ⨅ n : ℕ, LinearMap.range (fixedVectorsMap T K.toSubgroup ^ n) := by
  rw [Submodule.mem_iInf]
  intro n
  obtain ⟨y, hy, hyx⟩ := exists_fixed_preimage_pow hρ T K hK hx (mem_fittingRange_iff.mp hx₁ n)
  exact ⟨⟨y, hy⟩, Subtype.ext (by rw [fixedVectorsMap_pow_apply]; exact hyx)⟩

/-- Waldspurger, proof of Corollary III.7.2: for an admissible `ρ` and an intertwiner `T`,
`V = V₁ ⊕ V₂` with `V₁ = ⋂ₙ Tⁿ V` and `V₂ = ⋃ₙ Ker Tⁿ`. -/
theorem isCompl_fittingRange_fittingKernel (hρ : IsAdmissible ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (T : ρ.IntertwiningMap ρ) :
    IsCompl (fittingRange T).toSubmodule (fittingKernel T).toSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x h₁ h₂
    obtain ⟨K, hK, hx⟩ := exists_isCompact_fixed hρ.1 hcof x
    have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
    have hdisj :=
      (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (fixedVectorsMap T K.toSubgroup)).disjoint
    have h₂' : (⟨x, hx⟩ : fixedVectors ρ K.toSubgroup) ∈
        ⨆ n : ℕ, LinearMap.ker (fixedVectorsMap T K.toSubgroup ^ n) := by
      obtain ⟨m, hm⟩ := mem_fittingKernel_iff.mp h₂
      exact mem_iSup_ker_pow.mpr ⟨m, Subtype.ext (by rw [fixedVectorsMap_pow_apply]; exact hm)⟩
    have h0 := Submodule.disjoint_def.mp hdisj _ h₂'
      (mem_iInf_range_fixedVectorsMap_pow hρ.1 T K hK h₁ hx)
    exact congrArg Subtype.val h0
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    obtain ⟨K, hK, hx⟩ := exists_isCompact_fixed hρ.1 hcof x
    have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
    have hcod :=
      (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (fixedVectorsMap T K.toSubgroup)).codisjoint
    have hmem : (⟨x, hx⟩ : fixedVectors ρ K.toSubgroup) ∈
        (⨆ n : ℕ, LinearMap.ker (fixedVectorsMap T K.toSubgroup ^ n)) ⊔
          ⨅ n : ℕ, LinearMap.range (fixedVectorsMap T K.toSubgroup ^ n) := by
      rw [codisjoint_iff.mp hcod]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    refine Submodule.mem_sup.mpr ⟨b, ?_, a, ?_, ?_⟩
    · change (b : V) ∈ fittingRange T
      rw [mem_fittingRange_iff]
      intro n
      obtain ⟨c, hc⟩ := (Submodule.mem_iInf _).mp hb n
      exact ⟨c, by rw [← fixedVectorsMap_pow_apply, hc]⟩
    · change (a : V) ∈ fittingKernel T
      obtain ⟨m, hm⟩ := mem_iSup_ker_pow.mp ha
      exact mem_fittingKernel_iff.mpr ⟨m, by rw [← fixedVectorsMap_pow_apply, hm]; rfl⟩
    · rw [add_comm]
      exact congrArg Subtype.val hab

/-- Waldspurger, proof of Corollary III.7.2: `T` is bijective on `V₁` (`π₁(p)` is bijective). -/
theorem bijOn_fittingRange (hρ : IsAdmissible ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (T : ρ.IntertwiningMap ρ) :
    Set.BijOn T (fittingRange T) (fittingRange T) := by
  refine ⟨mapsTo_fittingRange T, ?_, ?_⟩
  · intro x hx y hy hxy
    have hd := (isCompl_fittingRange_fittingKernel hρ hcof T).disjoint
    have h₁ : x - y ∈ (fittingRange T).toSubmodule := sub_mem hx hy
    have h₂ : x - y ∈ (fittingKernel T).toSubmodule := by
      refine mem_fittingKernel_iff.mpr ⟨1, ?_⟩
      rw [pow_one, map_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h₁ h₂)
  · intro x hx
    obtain ⟨K, hK, hxK⟩ := exists_isCompact_fixed hρ.1 hcof x
    have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
    set TK := fixedVectorsMap T K.toSubgroup
    obtain ⟨N, hN⟩ := (LinearMap.eventually_iInf_range_pow_eq TK).exists
    have hx' := mem_iInf_range_fixedVectorsMap_pow hρ.1 T K hK hx hxK
    obtain ⟨c, hc⟩ := (Submodule.mem_iInf _).mp hx' (N + 1)
    refine ⟨((TK ^ N) c : V), ?_, ?_⟩
    · change ((TK ^ N) c : V) ∈ fittingRange T
      rw [mem_fittingRange_iff]
      intro m
      have hm : (TK ^ N) c ∈ ⨅ k : ℕ, LinearMap.range (TK ^ k) := by
        rw [hN]
        exact LinearMap.mem_range_self _ c
      obtain ⟨d, hd⟩ := (Submodule.mem_iInf _).mp hm m
      exact ⟨d, by rw [← fixedVectorsMap_pow_apply, hd]⟩
    · have h := congrArg Subtype.val hc
      rw [pow_succ', Module.End.mul_apply] at h
      exact h

end Langlands.HarishChandraSchwartz
