import Langlands.Representation.Jacquet.StationaryRangeLift
import Langlands.Representation.Jacquet.CompressionSplittingDuality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Stationary compression from a countable power family

Let `ρ` be a smooth complex representation with an Iwahori contraction `(K, N, M, Nbar, g)`,
`g` central in `M`. Suppose a smooth representation `σ` with intertwiners `q n : σ → ρ`
behaves like the countable power `ρ^ℕ` on `K`-fixed vectors and on `N`-coinvariants:
every family of `K`-fixed vectors comes from one `K`-fixed vector of `σ`, the coinvariant
images of the `q n` detect zero, and every family of `(K ∩ M)`-fixed coinvariant vectors is
realized by one vector of `σ`. Then the power ranges and kernels of compression by `g` on
`K`-fixed vectors of `ρ` are stationary, so the Fitting splitting holds.

Stationarity also passes from a transpose to the original endomorphism; applied to the
evaluation duality of compressions on the smooth contragredient, it gives the splitting for
compression by `g⁻¹` on `ρ` from stationarity for `g` on the contragredient.
-/

noncomputable section

namespace Langlands.Jacquet

universe uR uE uF uG uV uW

section Stationary

variable {R : Type uR} [Ring R] {E : Type uE} [AddCommGroup E] [Module R E]

/-- Power ranges decrease. -/
theorem range_pow_le_range_pow_of_le (f : Module.End R E) {a b : ℕ} (hab : a ≤ b) :
    LinearMap.range (f ^ b) ≤ LinearMap.range (f ^ a) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

/-- Power kernels increase. -/
theorem ker_pow_le_ker_pow_of_le (f : Module.End R E) {a b : ℕ} (hab : a ≤ b) :
    LinearMap.ker (f ^ a) ≤ LinearMap.ker (f ^ b) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, pow_add, Module.End.mul_eq_comp]
  exact LinearMap.ker_le_ker_comp _ _

/-- Power ranges and kernels constant from `b` on are the intersection of all ranges and
the union of all kernels from `b` on. -/
theorem iInf_range_iSup_ker_of_stationary (f : Module.End R E) (b : ℕ)
    (hb : ∀ s, b ≤ s → LinearMap.range (f ^ s) = LinearMap.range (f ^ b) ∧
      LinearMap.ker (f ^ s) = LinearMap.ker (f ^ b)) :
    ∀ s, b ≤ s → (⨅ n : ℕ, LinearMap.range (f ^ n)) = LinearMap.range (f ^ s) ∧
      (⨆ n : ℕ, LinearMap.ker (f ^ n)) = LinearMap.ker (f ^ s) := by
  intro s hs
  rw [(hb s hs).1, (hb s hs).2]
  constructor
  · apply le_antisymm (iInf_le _ b)
    refine le_iInf fun n => ?_
    rcases le_total n b with hn | hn
    · exact range_pow_le_range_pow_of_le f hn
    · exact (hb n hn).1.ge
  · apply le_antisymm _ (le_iSup (fun n : ℕ => LinearMap.ker (f ^ n)) b)
    refine iSup_le fun n => ?_
    rcases le_total n b with hn | hn
    · exact ker_pow_le_ker_pow_of_le f hn
    · exact (hb n hn).2.le

end Stationary

section Transpose

variable {k : Type uR} [Field k] {E : Type uE} [AddCommGroup E] [Module k E]
  {F : Type uF} [AddCommGroup F] [Module k F]

/-- Over a field, stationarity of the power ranges and kernels passes from an endomorphism
identified with the transpose by a bijection onto the full dual. Kernels of powers are the
annihilators of the transposed ranges, and ranges of powers are the annihilators of the
transposed kernels. -/
theorem stationary_of_transpose (f : Module.End k E) (f' : Module.End k F)
    (p : F →ₗ[k] Module.Dual k E) (hp : Function.Bijective p)
    (hadj : ∀ ℓ v, p (f' ℓ) v = p ℓ (f v)) (b : ℕ)
    (hb : ∀ s, b ≤ s → LinearMap.range (f' ^ s) = LinearMap.range (f' ^ b) ∧
      LinearMap.ker (f' ^ s) = LinearMap.ker (f' ^ b)) :
    ∀ s, b ≤ s → LinearMap.range (f ^ s) = LinearMap.range (f ^ b) ∧
      LinearMap.ker (f ^ s) = LinearMap.ker (f ^ b) := by
  have hpow : ∀ n ℓ v, p ((f' ^ n) ℓ) v = p ℓ ((f ^ n) v) := by
    intro n
    induction n with
    | zero => intro ℓ v; rfl
    | succ n ih =>
      intro ℓ v
      rw [pow_succ', Module.End.mul_apply, hadj, ih, pow_succ, Module.End.mul_apply]
  have hker : ∀ n v, v ∈ LinearMap.ker (f ^ n) ↔
      ∀ μ ∈ LinearMap.range (f' ^ n), p μ v = 0 := by
    intro n v
    rw [LinearMap.mem_ker]
    constructor
    · rintro hv _ ⟨ℓ, rfl⟩
      rw [hpow, hv, map_zero]
    · intro h
      rw [← Module.forall_dual_apply_eq_zero_iff k]
      intro φ
      obtain ⟨ℓ, rfl⟩ := hp.2 φ
      rw [← hpow]
      exact h _ ⟨ℓ, rfl⟩
  have hrange : ∀ n v, v ∈ LinearMap.range (f ^ n) ↔
      ∀ ℓ ∈ LinearMap.ker (f' ^ n), p ℓ v = 0 := by
    intro n v
    constructor
    · rintro ⟨u, rfl⟩ ℓ hℓ
      rw [← hpow, LinearMap.mem_ker.mp hℓ, map_zero, LinearMap.zero_apply]
    · intro h
      by_contra hv
      obtain ⟨φ, hφv, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
      obtain ⟨ℓ, rfl⟩ := hp.2 φ
      apply hφv
      apply h
      rw [LinearMap.mem_ker]
      apply hp.1
      rw [map_zero]
      refine LinearMap.ext fun u => ?_
      rw [hpow, LinearMap.zero_apply]
      have hm : p ℓ ((f ^ n) u) ∈ (LinearMap.range (f ^ n)).map (p ℓ) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ u)
      rw [hφ, Submodule.mem_bot] at hm
      exact hm
  intro s hs
  obtain ⟨hR, hK⟩ := hb s hs
  constructor
  · ext v
    rw [hrange, hrange, hK]
  · ext v
    rw [hker, hker, hR]

end Transpose

section Core

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Compression by a central Iwahori-contracting element has stationary power ranges and
kernels on `K`-fixed vectors, given a power family `q n : σ → ρ` that realizes all families
of `K`-fixed vectors (`hlift`), detects zero on coinvariants (`hinj`), and realizes all
families of Levi-fixed coinvariant vectors (`hsurj`). -/
theorem stationary_of_powerFamily (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {N M Nbar : Subgroup G} {g : G} (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hcen : ∀ m ∈ M, m * g = g * m)
    (q : ℕ → σ.IntertwiningMap ρ)
    (hlift : ∀ x : ℕ → fixedVectors ρ K.toSubgroup,
      ∃ w : fixedVectors σ K.toSubgroup, ∀ n, q n (w : W) = x n)
    (hinj : ∀ w : W, (∀ n, mk ρ N (q n w) = 0) → mk σ N w = 0)
    (hsurj : ∀ y : ℕ → fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype),
      ∃ w : W, ∀ n, mk ρ N (q n w) = y n) :
    ∃ b, ∀ s, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
          LinearMap.range (compressedAction ρ hρ K hK g ^ b) ∧
        LinearMap.ker (compressedAction ρ hρ K hK g ^ s) =
          LinearMap.ker (compressedAction ρ hρ K hK g ^ b) := by
  set c := compressedAction ρ hρ K hK g with hc_def
  set cσ := compressedAction σ hσ K hK g with hcσ_def
  let gM : M := ⟨g, h.mem_levi⟩
  have hnat : ∀ n r (w : fixedVectors σ K.toSubgroup),
      fixedVectorsMap (q n) K.toSubgroup ((cσ ^ r) w) =
        (c ^ r) (fixedVectorsMap (q n) K.toSubgroup w) := by
    intro n r w
    have hcomm := Module.End.commute_pow_left_of_commute
      (compressedAction_natural σ ρ hσ hρ K hK g (q n)).symm r
    exact (LinearMap.congr_fun hcomm w).symm
  -- Step 1: the kernel of the Jacquet map is killed by one fixed power.
  have htors : ∃ b, ∀ x : fixedVectors ρ K.toSubgroup, mk ρ N (x : V) = 0 → (c ^ b) x = 0 := by
    by_contra hcon
    push Not at hcon
    choose x hx0 hxne using hcon
    obtain ⟨w, hw⟩ := hlift x
    have hw0 : mk σ N (w : W) = 0 := hinj w fun n => by rw [hw n]; exact hx0 n
    have hwker : w ∈ powerKernelSup σ hσ K hK g := by
      rw [powerKernelSup_eq_ker_of_iwahoriContraction σ hσ hK h hMN, LinearMap.mem_ker]
      exact Subtype.ext hw0
    have hwker' : w ∈ ⨆ r : ℕ, LinearMap.ker (cσ ^ r) := hwker
    obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _
      (Monotone.directed_le fun a b hab => ker_pow_le_ker_pow_of_le cσ hab)).mp hwker'
    apply hxne r
    have hq : fixedVectorsMap (q r) K.toSubgroup w = x r := Subtype.ext (hw r)
    rw [← hq, ← hnat, LinearMap.mem_ker.mp hr, map_zero]
  -- Levi-fixed coinvariant vectors stay fixed under powers of `g⁻¹`, by centrality.
  have hcomm : ∀ m : M, Commute m gM := fun m => Subtype.ext (hcen m m.2)
  have hpres : ∀ y : Coinvariants ρ N,
      (∀ k : K.toSubgroup.comap M.subtype, action ρ N M hMN k y = y) →
      ∀ n : ℕ, ∀ k : K.toSubgroup.comap M.subtype,
        action ρ N M hMN k (action ρ N M hMN (gM⁻¹ ^ n) y) =
          action ρ N M hMN (gM⁻¹ ^ n) y := by
    intro y hy n k
    rw [← Module.End.mul_apply, ← map_mul, ((hcomm (k : M)).inv_right.pow_right n).eq,
      map_mul, Module.End.mul_apply, hy k]
  -- Step 2: the Jacquet map on `K`-fixed vectors is onto the Levi-fixed vectors.
  have honto : ∀ y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype),
      ∃ x : fixedVectors ρ K.toSubgroup, mk ρ N (x : V) = y := by
    intro y
    let yn : ℕ → fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
      fun n => ⟨action ρ N M hMN (gM⁻¹ ^ n) y, fun k => hpres y (fun k => y.property k) n k⟩
    obtain ⟨w, hw⟩ := hsurj yn
    have hwfix : ∀ k : K.toSubgroup.comap M.subtype,
        action σ N M hMN k (mk σ N w) = mk σ N w := by
      intro k
      rw [action_mk, ← sub_eq_zero, ← map_sub]
      apply hinj
      intro n
      rw [map_sub, map_sub, sub_eq_zero, (q n).isIntertwining _ _ ((k : M) : G) w,
        ← action_mk ρ N M hMN (k : M), hw n]
      exact (yn n).property k
    obtain ⟨s, x, hx⟩ := exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction σ hσ hK h
      hMN ⟨mk σ N w, fun k => hwfix k⟩
    refine ⟨fixedVectorsMap (q s) K.toSubgroup x, ?_⟩
    change mk ρ N (q s (x : W)) = y
    calc mk ρ N (q s (x : W))
        = map N M hMN (q s) (mk σ N (x : W)) := (map_mk N M hMN (q s) _).symm
      _ = map N M hMN (q s) (action σ N M hMN (gM ^ s) (mk σ N w)) := by rw [hx]
      _ = action ρ N M hMN (gM ^ s) (map N M hMN (q s) (mk σ N w)) :=
          (map N M hMN (q s)).isIntertwining _ _ _ _
      _ = action ρ N M hMN (gM ^ s) (action ρ N M hMN (gM⁻¹ ^ s) y) := by
          rw [map_mk, hw s]
      _ = y := by
          rw [← Module.End.mul_apply, ← map_mul, inv_pow, mul_inv_cancel, map_one,
            Module.End.one_apply]
  -- Step 3: stationarity from the torsion bound.
  obtain ⟨b, hb⟩ := htors
  refine ⟨b, fun s hs => ⟨le_antisymm (range_pow_le_range_pow_of_le c hs) ?_,
    le_antisymm ?_ (ker_pow_le_ker_pow_of_le c hs)⟩⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
    have hxfix := (fixedJacquetMap ρ N M hMN K.toSubgroup x).property
    obtain ⟨z, hz⟩ := honto ⟨action ρ N M hMN (gM⁻¹ ^ t) (mk ρ N (x : V)),
      fun k => hpres _ (fun k => hxfix k) t k⟩
    refine ⟨z, ?_⟩
    have hmk : mk ρ N (((c ^ t) z : fixedVectors ρ K.toSubgroup) : V) = mk ρ N (x : V) := by
      rw [mk_compressedAction_pow_of_iwahoriContraction ρ hρ hK h hMN t z, hz]
      change action ρ N M hMN (gM ^ t) (action ρ N M hMN (gM⁻¹ ^ t) (mk ρ N (x : V))) = _
      rw [← Module.End.mul_apply, ← map_mul, inv_pow, mul_inv_cancel, map_one,
        Module.End.one_apply]
    have h0 := hb (x - (c ^ t) z) (by rw [Submodule.coe_sub, map_sub, hmk, sub_self])
    rw [map_sub, sub_eq_zero] at h0
    rw [pow_add, Module.End.mul_apply, h0]
  · intro v hv
    have hv' : v ∈ powerKernelSup ρ hρ K hK g :=
      Submodule.mem_iSup_of_mem (p := fun r : ℕ => LinearMap.ker (c ^ r)) s hv
    rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN, LinearMap.mem_ker] at hv'
    exact hb v (congrArg Subtype.val hv')

/-- Stationary power ranges and kernels of compression give its Fitting splitting. -/
theorem compactCompressionSplits_of_stationary (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ)
    (hb : ∀ s, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
          LinearMap.range (compressedAction ρ hρ K hK g ^ b) ∧
        LinearMap.ker (compressedAction ρ hρ K hK g ^ s) =
          LinearMap.ker (compressedAction ρ hρ K hK g ^ b)) :
    CompactCompressionSplits ρ hρ K hK g :=
  compactCompressionSplits_of_eventuallyStable ρ hρ K hK g
    ⟨b, iInf_range_iSup_ker_of_stationary _ b hb⟩

/-- The Fitting splitting for compression by a central Iwahori-contracting element, from a
power family as in `stationary_of_powerFamily`. -/
theorem compactCompressionSplits_of_powerFamily (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {N M Nbar : Subgroup G} {g : G} (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hcen : ∀ m ∈ M, m * g = g * m)
    (q : ℕ → σ.IntertwiningMap ρ)
    (hlift : ∀ x : ℕ → fixedVectors ρ K.toSubgroup,
      ∃ w : fixedVectors σ K.toSubgroup, ∀ n, q n (w : W) = x n)
    (hinj : ∀ w : W, (∀ n, mk ρ N (q n w) = 0) → mk σ N w = 0)
    (hsurj : ∀ y : ℕ → fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype),
      ∃ w : W, ∀ n, mk ρ N (q n w) = y n) :
    CompactCompressionSplits ρ hρ K hK g := by
  obtain ⟨b, hb⟩ := stationary_of_powerFamily ρ σ hρ hσ hK h hMN hcen q hlift hinj hsurj
  exact compactCompressionSplits_of_stationary ρ hρ K hK g b hb

/-- Stationary compression by `g` on the `K`-fixed smooth functionals gives the Fitting
splitting for compression by `g⁻¹` on the `K`-fixed vectors, through the evaluation
duality `smoothDualFixedRestriction` and `compressedAction_adjoint`. -/
theorem compactCompressionSplits_inv_of_contragredient_stationary
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) (b : ℕ)
    (hb : ∀ s, b ≤ s →
      LinearMap.range (compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K hK g ^ s) =
        LinearMap.range (compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K hK g ^ b) ∧
      LinearMap.ker (compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K hK g ^ s) =
        LinearMap.ker (compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K hK g ^ b)) :
    CompactCompressionSplits ρ hρ K hK g⁻¹ := by
  have hadj : ∀ ℓ v,
      smoothDualFixedRestriction ρ K.toSubgroup
          (compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
            K hK g ℓ) v =
        smoothDualFixedRestriction ρ K.toSubgroup ℓ (compressedAction ρ hρ K hK g⁻¹ v) := by
    intro ℓ v
    simpa only [inv_inv] using compressedAction_adjoint ρ hρ K hK g⁻¹ ℓ v
  have hst := stationary_of_transpose (k := ℂ) (E := fixedVectors ρ K.toSubgroup)
    (F := fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (compressedAction ρ hρ K hK g⁻¹)
    (compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g)
    (smoothDualFixedRestriction ρ K.toSubgroup)
    (smoothDualFixedRestriction_bijective ρ hρ K hK) hadj b hb
  exact compactCompressionSplits_of_eventuallyStable ρ hρ K hK g⁻¹
    ⟨b, iInf_range_iSup_ker_of_stationary _ b hst⟩

end Core

end Langlands.Jacquet
