import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Finite image of inertia from a tame Frobenius structure

`finite_image_of_tameFrobenius` is an abstract form of Grothendieck's monodromy argument for
an irreducible representation (Tate, *Number theoretic background*, (4.1.5) and (4.2)). The
group `G` has a topology in which every neighbourhood of `1` contains a normal subgroup of
finite index. A normal subgroup `I` and an element `φ` satisfy: for every neighbourhood `U`
of `1`, some set `P` contains the commutators of `I` and the elements `φ x φ⁻¹ x⁻ᑫ` with
`x ∈ I`, and every element of `P` has a `p`-power power in `U`; here `q ≥ 2`. Let `ℓ` be a
prime coprime to `p`. A continuous irreducible representation on a finite-dimensional space
over an algebraically closed ultrametric field `E` with `0 < ‖(ℓ : E)‖ < 1` then has finite
image on `I`.

The congruence sets `congruenceSet b ρ ‖ℓ‖ j` (all matrix entries of `ρ g - 1` in a basis
`b` of norm at most `‖ℓ‖ ^ j`) play the role of the `ℓ`-adic congruence subgroups; no
lattice and no finite coefficient field is used.
-/

noncomputable section

namespace Langlands.LadicMonodromy

open Filter Topology

section Entries

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {V : Type*} [AddCommGroup V] [Module E V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)

/-- All matrix entries of `f` in the basis `b` have norm at most `r`. -/
def EntriesLE (r : ℝ) (f : Module.End E V) : Prop :=
  ∀ i j, ‖LinearMap.toMatrixAlgEquiv b f i j‖ ≤ r

variable {b}

omit [IsUltrametricDist E] in
theorem EntriesLE.mono {r s : ℝ} {f : Module.End E V} (h : EntriesLE b r f) (hrs : r ≤ s) :
    EntriesLE b s f :=
  fun i j => (h i j).trans hrs

theorem EntriesLE.add {r : ℝ} {f g : Module.End E V} (hf : EntriesLE b r f)
    (hg : EntriesLE b r g) : EntriesLE b r (f + g) := by
  intro i j
  rw [map_add, Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf i j) (hg i j))

omit [IsUltrametricDist E] in
theorem EntriesLE.neg {r : ℝ} {f : Module.End E V} (hf : EntriesLE b r f) :
    EntriesLE b r (-f) := by
  intro i j
  rw [map_neg, Matrix.neg_apply, norm_neg]
  exact hf i j

theorem EntriesLE.sub {r : ℝ} {f g : Module.End E V} (hf : EntriesLE b r f)
    (hg : EntriesLE b r g) : EntriesLE b r (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem EntriesLE.mul {r s : ℝ} {f g : Module.End E V} (hf : EntriesLE b r f)
    (hg : EntriesLE b s g) (hr : 0 ≤ r) (hs : 0 ≤ s) : EntriesLE b (r * s) (f * g) := by
  intro i j
  rw [map_mul, Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf i k) (hg k j) (norm_nonneg _) hr

omit [IsUltrametricDist E] in
theorem EntriesLE.smul {r : ℝ} {f : Module.End E V} (c : E) (hf : EntriesLE b r f) :
    EntriesLE b (‖c‖ * r) (c • f) := by
  intro i j
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hf i j) (norm_nonneg c)

omit [IsUltrametricDist E] in
theorem EntriesLE.of_smul {r : ℝ} {f : Module.End E V} {c : E} (hc : c ≠ 0)
    (hf : EntriesLE b (‖c‖ * r) (c • f)) : EntriesLE b r f := by
  intro i j
  have h := hf i j
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, norm_mul] at h
  exact le_of_mul_le_mul_left h (norm_pos_iff.mpr hc)

theorem EntriesLE.nsmul {r : ℝ} {f : Module.End E V} (n : ℕ) (hf : EntriesLE b r f)
    (hr : 0 ≤ r) : EntriesLE b r (n • f) := by
  rw [← Nat.cast_smul_eq_nsmul E]
  refine (hf.smul (n : E)).mono ?_
  exact mul_le_of_le_one_left hr (IsUltrametricDist.norm_natCast_le_one E n)

omit [IsUltrametricDist E] in
theorem entriesLE_one : EntriesLE b 1 (1 : Module.End E V) := by
  intro i j
  rw [map_one, Matrix.one_apply]
  split_ifs <;> simp

omit [IsUltrametricDist E] in
theorem entriesLE_zero {r : ℝ} (hr : 0 ≤ r) : EntriesLE b r (0 : Module.End E V) := by
  intro i j
  simpa using hr

theorem EntriesLE.pow {r : ℝ} {f : Module.End E V} (hf : EntriesLE b r f)
    (hr1 : r ≤ 1) (n : ℕ) : EntriesLE b 1 (f ^ n) := by
  induction n with
  | zero => simpa using entriesLE_one
  | succ n ih =>
    rw [pow_succ]
    simpa using ih.mul (hf.mono hr1) zero_le_one zero_le_one

/-- Second-order binomial bound: if the entries of `X` have norm at most `r ≤ 1`, then
those of `(1 + X) ^ n - 1 - n • X` have norm at most `r * r`. -/
theorem entriesLE_one_add_pow_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {X : Module.End E V}
    (hX : EntriesLE b r X) (n : ℕ) :
    EntriesLE b (r * r) ((1 + X) ^ n - 1 - n • X) := by
  induction n with
  | zero => simpa using entriesLE_zero (b := b) (mul_nonneg hr0 hr0)
  | succ n ih =>
    have e : (1 + X) ^ (n + 1) - 1 - (n + 1) • X =
        ((1 + X) ^ n - 1 - n • X) * (1 + X) + n • (X * X) := by
      simp only [pow_succ, add_smul, one_smul, nsmul_eq_mul]
      noncomm_ring
    rw [e]
    have h1 : EntriesLE b 1 (1 + X) := entriesLE_one.add (hX.mono hr1)
    refine EntriesLE.add ?_ ((hX.mul hX hr0 hr0).nsmul n (mul_nonneg hr0 hr0))
    simpa using ih.mul h1 (mul_nonneg hr0 hr0) zero_le_one

omit [IsUltrametricDist E] in
theorem eq_zero_of_forall_entriesLE {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {f : Module.End E V} (hf : ∀ j : ℕ, EntriesLE b (lam ^ j) f) : f = 0 := by
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [map_zero]
  ext i k
  rw [Matrix.zero_apply, ← norm_le_zero_iff]
  exact ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1)
    (Eventually.of_forall fun j => hf j i k)

theorem entriesLE_sub_one_mem_nhds {r : ℝ} (hr : 0 < r) :
    letI : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
    {f : Module.End E V | EntriesLE b r (f - 1)} ∈ 𝓝 (1 : Module.End E V) := by
  let : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
  have : IsModuleTopology E (Module.End E V) := ⟨rfl⟩
  have hev : ∀ i j, ∀ᶠ f in 𝓝 (1 : Module.End E V),
      ‖LinearMap.toMatrixAlgEquiv b (f - 1) i j‖ < r := by
    intro i j
    let c : Module.End E V →ₗ[E] E := (LinearMap.proj j).comp
      ((LinearMap.proj i).comp (LinearMap.toMatrixAlgEquiv b).toLinearMap)
    have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c
    have hcf : Continuous fun f : Module.End E V =>
        ‖LinearMap.toMatrixAlgEquiv b (f - 1) i j‖ := by
      have : (fun f : Module.End E V => ‖LinearMap.toMatrixAlgEquiv b (f - 1) i j‖) =
          fun f => ‖c f - c 1‖ := by
        funext f
        rw [← map_sub]
        rfl
      rw [this]
      exact (hc.sub continuous_const).norm
    exact hcf.continuousAt.eventually_lt continuousAt_const (by simpa using hr)
  filter_upwards [Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hev i)]
    with f hf i j
  exact (hf i j).le

end Entries


section Spectral

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

open Module.End

/-- An eigenvalue of a conjugate `P * f * Q`, with `Q` inverse to `P`, is an eigenvalue of `f`. -/
theorem hasEigenvalue_of_conj {f P Q : Module.End E V} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {μ : E} (hμ : (P * f * Q).HasEigenvalue μ) : f.HasEigenvalue μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hfv : P (f (Q v)) = μ • v := hv.apply_eq_smul
  have hQv : Q v ≠ 0 := by
    intro h
    apply hv.2
    have : (P * Q) v = v := by rw [hPQ]; rfl
    rw [← this, Module.End.mul_apply, h, map_zero]
  refine hasEigenvalue_of_hasEigenvector (x := Q v) ⟨mem_eigenspace_iff.mpr ?_, hQv⟩
  have : (Q * P) (f (Q v)) = f (Q v) := by rw [hQP]; rfl
  rw [← this, Module.End.mul_apply, hfv, map_smul]

variable [FiniteDimensional E V]

/-- If `Φ T Φ⁻¹ = T ^ q` with `q ≥ 2` and `T` invertible, then for some positive `m` every
eigenvalue of `T ^ m` equals `1`, that is, the spectrum of `T ^ m` is contained in `{1}`.
It is empty when `V` is zero. -/
theorem exists_pow_eigenvalue_eq_one [IsAlgClosed E] {T P Q : Module.End E V} (hT : IsUnit T)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) {q : ℕ} (hq : 2 ≤ q) (hconj : P * T * Q = T ^ q) :
    ∃ m : ℕ, 0 < m ∧ ∀ μ : E, (T ^ m).HasEigenvalue μ → μ = 1 := by
  set S := spectrum E T with hS
  have hSfin : S.Finite := Module.End.finite_spectrum T
  have h0 : ∀ s ∈ S, s ≠ 0 := fun s hs h => spectrum.zero_notMem E hT (h ▸ hs)
  have hmaps : ∀ s ∈ S, s ^ q ∈ S := by
    intro s hs
    have h1 : s ^ q ∈ spectrum E (T ^ q) := spectrum.pow_mem_pow T q hs
    rw [← hconj, ← Module.End.hasEigenvalue_iff_mem_spectrum] at h1
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp (hasEigenvalue_of_conj hPQ hQP h1)
  have hiter : ∀ k : ℕ, ∀ s ∈ S, s ^ (q ^ k) ∈ S := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro s hs
      rw [pow_succ, pow_mul]
      exact hmaps _ (ih s hs)
  have : Finite S := hSfin.to_subtype
  let F : ℕ → (S → S) := fun k s => ⟨s.1 ^ (q ^ k), hiter k s.1 s.2⟩
  have hclaim : ∀ i j : ℕ, i < j → F i = F j → ∃ m : ℕ, 0 < m ∧ ∀ s ∈ S, s ^ m = 1 := by
    intro i j hij hF
    have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
    refine ⟨q ^ j - q ^ i, Nat.sub_pos_of_lt hlt, fun s hs => ?_⟩
    have h1 : s ^ (q ^ i) = s ^ (q ^ j) := congrArg Subtype.val (congrFun hF ⟨s, hs⟩)
    have h2 : s ^ (q ^ j) = s ^ (q ^ i) * s ^ (q ^ j - q ^ i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [h2] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ (h0 s hs)) (h1.symm.trans (mul_one _).symm)
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  obtain ⟨m, hm, hmS⟩ : ∃ m : ℕ, 0 < m ∧ ∀ s ∈ S, s ^ m = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hclaim i j h hF
    · exact hclaim j i h hF.symm
  refine ⟨m, hm, fun μ hμ => ?_⟩
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum.map_pow_of_pos T hm] at hμ
  obtain ⟨s, hs, rfl⟩ := hμ
  exact hmS s hs

/-- On a nonzero space, pairwise commuting endomorphisms all of whose eigenvalues equal `1`
have a common nonzero fixed vector. -/
theorem exists_common_fixed [IsAlgClosed E] [Nontrivial V] (S : Set (Module.End E V))
    (hcomm : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f)
    (heig : ∀ f ∈ S, ∀ μ : E, f.HasEigenvalue μ → μ = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ f ∈ S, f v = v := by
  let 𝒲 : Set (Submodule E V) := {W | W ≠ ⊥ ∧ ∀ f ∈ S, ∀ w ∈ W, f w ∈ W}
  have hne : 𝒲.Nonempty := ⟨⊤, top_ne_bot, fun _ _ _ _ => Submodule.mem_top⟩
  obtain ⟨W₀, ⟨hW₀, hinv⟩, hmin⟩ := (wellFounded_lt (α := Submodule E V)).has_min 𝒲 hne
  have key : ∀ f ∈ S, ∀ w ∈ W₀, f w = w := by
    intro f hf
    let W₁ : Submodule E V := W₀ ⊓ LinearMap.ker (f - 1)
    have hW₁ : W₁ ∈ 𝒲 := by
      refine ⟨?_, ?_⟩
      · have : Nontrivial W₀ := Submodule.nontrivial_iff_ne_bot.mpr hW₀
        let fr : Module.End E W₀ := f.restrict (fun w hw => hinv f hf w hw)
        obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue fr
        obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
        have hfw : f w = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
        have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
        have hμ1 : μ = 1 := heig f hf μ
          (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hfw, hw0⟩)
        rw [hμ1, one_smul] at hfw
        intro hbot
        apply hw0
        have hmem : (w : V) ∈ W₁ := by
          refine Submodule.mem_inf.mpr ⟨w.2, ?_⟩
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hfw, sub_self]
        rw [hbot] at hmem
        exact (Submodule.mem_bot E).mp hmem
      · intro g hg w hw
        obtain ⟨hw₀, hwk⟩ := Submodule.mem_inf.mp hw
        refine Submodule.mem_inf.mpr ⟨hinv g hg w hw₀, ?_⟩
        rw [LinearMap.mem_ker] at hwk ⊢
        have : (f - 1) (g w) = g ((f - 1) w) := by
          simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
          rw [← Module.End.mul_apply, hcomm f hf g hg, Module.End.mul_apply]
        rw [this, hwk, map_zero]
    have heq : W₁ = W₀ := by
      by_contra hne
      exact hmin W₁ hW₁ (lt_of_le_of_ne inf_le_left hne)
    intro w hw
    have hw1 : w ∈ W₁ := heq ▸ hw
    have h := (Submodule.mem_inf.mp hw1).2
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀
  exact ⟨v, hv0, fun f hf => key f hf v hv⟩

end Spectral

section Group

variable {G : Type*} [Group G]

/-- A set containing `1`, closed under multiplication and containing a normal subgroup of
finite index is closed under inverses. -/
theorem inv_mem_of_normal_finiteIndex_subset {S : Set G} (hone : (1 : G) ∈ S)
    (hmul : ∀ g h : G, g ∈ S → h ∈ S → g * h ∈ S) {N : Subgroup G} [N.Normal] [N.FiniteIndex]
    (hNS : (N : Set G) ⊆ S) {g : G} (hg : g ∈ S) : g⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, g ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ _ ih hg
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
  have hk := N.pow_index_mem g
  rw [hm, pow_succ'] at hk
  have e : g⁻¹ = g ^ m * (g * g ^ m)⁻¹ := by
    rw [mul_inv_rev, mul_inv_cancel_left]
  rw [e]
  exact hmul _ _ (hpow m) (hNS (N.inv_mem hk))

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {V : Type*} [AddCommGroup V] [Module E V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V) (ρ : G →* Module.End E V)

/-- The elements `g` such that every matrix entry of `ρ g - 1` in the basis `b` has norm at
most `lam ^ j`. -/
def congruenceSet (lam : ℝ) (j : ℕ) : Set G := {g | EntriesLE b (lam ^ j) (ρ g - 1)}

variable {b ρ}

omit [IsUltrametricDist E] in
theorem one_mem_congruenceSet {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    (1 : G) ∈ congruenceSet b ρ lam j := by
  change EntriesLE b (lam ^ j) (ρ 1 - 1)
  rw [map_one, sub_self]
  exact entriesLE_zero (pow_nonneg hlam j)

theorem mul_mem_congruenceSet {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {j : ℕ} {g h : G}
    (hg : g ∈ congruenceSet b ρ lam j) (hh : h ∈ congruenceSet b ρ lam j) :
    g * h ∈ congruenceSet b ρ lam j := by
  have e : ρ (g * h) - 1 = (ρ g - 1) * (ρ h - 1) + ((ρ g - 1) + (ρ h - 1)) := by
    rw [map_mul]
    noncomm_ring
  change EntriesLE b (lam ^ j) (ρ (g * h) - 1)
  rw [e]
  have hj0 := pow_nonneg hlam0 j
  have hj1 : lam ^ j ≤ 1 := pow_le_one₀ hlam0 hlam1
  exact ((EntriesLE.mul hg hh hj0 hj0).mono (mul_le_of_le_one_left hj0 hj1)).add
    (EntriesLE.add hg hh)

variable [TopologicalSpace G]

theorem congruenceSet_mem_nhds
    (hρ : @Continuous G (Module.End E V) _ (moduleTopology E (Module.End E V)) ρ)
    {lam : ℝ} (hlam : 0 < lam) (j : ℕ) : congruenceSet b ρ lam j ∈ 𝓝 (1 : G) := by
  let : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
  have h := entriesLE_sub_one_mem_nhds (b := b) (pow_pos hlam j)
  have hc := hρ.continuousAt (x := 1)
  rw [ContinuousAt, map_one] at hc
  exact hc h

variable (b ρ)

/-- The congruence subgroup of level `j`: a subgroup as soon as every neighbourhood of `1`
contains a normal subgroup of finite index. -/
def congruenceSubgroup {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hρ : @Continuous G (Module.End E V) _ (moduleTopology E (Module.End E V)) ρ)
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ (N : Set G) ⊆ U)
    (j : ℕ) : Subgroup G where
  carrier := congruenceSet b ρ lam j
  one_mem' := one_mem_congruenceSet hlam0.le j
  mul_mem' := mul_mem_congruenceSet hlam0.le hlam1
  inv_mem' := by
    intro g hg
    obtain ⟨N, hNn, hNf, hNU⟩ := hN _ (congruenceSet_mem_nhds (b := b) hρ hlam0 j)
    exact inv_mem_of_normal_finiteIndex_subset (one_mem_congruenceSet hlam0.le j)
      (fun _ _ => mul_mem_congruenceSet hlam0.le hlam1) hNU hg

end Group


section Congruence

variable {G : Type*} [Group G]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {V : Type*} [AddCommGroup V] [Module E V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι E V} {ρ : G →* Module.End E V}

omit [IsUltrametricDist E] in
theorem congruenceSet_antitone {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : congruenceSet b ρ lam k ⊆ congruenceSet b ρ lam j :=
  fun _ hg => EntriesLE.mono hg (pow_le_pow_of_le_one hlam0 hlam1 hjk)

omit [IsUltrametricDist E] in
theorem mem_congruenceSet_of_eq_one {lam : ℝ} (hlam0 : 0 ≤ lam) {g : G} (h : ρ g = 1) (j : ℕ) :
    g ∈ congruenceSet b ρ lam j := by
  change EntriesLE b (lam ^ j) (ρ g - 1)
  rw [h, sub_self]
  exact entriesLE_zero (pow_nonneg hlam0 j)

omit [IsUltrametricDist E] in
theorem eq_one_of_forall_mem_congruenceSet {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {g : G} (hg : ∀ j, g ∈ congruenceSet b ρ lam j) : ρ g = 1 :=
  sub_eq_zero.mp (eq_zero_of_forall_entriesLE hlam0 hlam1 hg)

variable {ℓ : ℕ}

/-- If `g` is congruent to `1` modulo `ℓ ^ j` with `j ≥ 1`, then `g ^ ℓ` is congruent to `1`
modulo `ℓ ^ (j + 1)`. -/
theorem pow_mem_congruenceSet_succ (hℓ1 : ‖(ℓ : E)‖ < 1) {j : ℕ} (hj : 1 ≤ j) {g : G}
    (hg : g ∈ congruenceSet b ρ ‖(ℓ : E)‖ j) :
    g ^ ℓ ∈ congruenceSet b ρ ‖(ℓ : E)‖ (j + 1) := by
  set lam := ‖(ℓ : E)‖
  set X := ρ g - 1 with hX
  have hgX : EntriesLE b (lam ^ j) X := hg
  have hρg : ρ g = 1 + X := by rw [hX]; abel
  have hlam0 : 0 ≤ lam := norm_nonneg _
  have hj0 : 0 ≤ lam ^ j := pow_nonneg hlam0 j
  have hj1 : lam ^ j ≤ 1 := pow_le_one₀ hlam0 hℓ1.le
  have e : ρ (g ^ ℓ) - 1 = ((1 + X) ^ ℓ - 1 - ℓ • X) + (ℓ : E) • X := by
    rw [map_pow, hρg, Nat.cast_smul_eq_nsmul]
    abel
  change EntriesLE b (lam ^ (j + 1)) (ρ (g ^ ℓ) - 1)
  rw [e]
  refine EntriesLE.add ?_ ?_
  · refine (entriesLE_one_add_pow_sub hj0 hj1 hgX ℓ).mono ?_
    rw [← pow_add]
    exact pow_le_pow_of_le_one hlam0 hℓ1.le (by omega)
  · have h := hgX.smul (ℓ : E)
    rwa [← pow_succ'] at h

/-- An element congruent to `1` modulo `ℓ ^ j` with `j ≥ 2` whose image has order dividing
`ℓ` is congruent to `1` modulo `ℓ ^ (j + 1)`. -/
theorem mem_congruenceSet_succ_of_pow_eq_one (hℓ0 : (ℓ : E) ≠ 0) (hℓ1 : ‖(ℓ : E)‖ < 1)
    {j : ℕ} (hj : 2 ≤ j) {g : G} (hg : g ∈ congruenceSet b ρ ‖(ℓ : E)‖ j)
    (h : ρ g ^ ℓ = 1) : g ∈ congruenceSet b ρ ‖(ℓ : E)‖ (j + 1) := by
  set lam := ‖(ℓ : E)‖
  set X := ρ g - 1 with hX
  have hgX : EntriesLE b (lam ^ j) X := hg
  have hρg : ρ g = 1 + X := by rw [hX]; abel
  have hlam0 : 0 ≤ lam := norm_nonneg _
  have hj0 : 0 ≤ lam ^ j := pow_nonneg hlam0 j
  have hj1 : lam ^ j ≤ 1 := pow_le_one₀ hlam0 hℓ1.le
  have e : (ℓ : E) • X = -((1 + X) ^ ℓ - 1 - ℓ • X) := by
    rw [← hρg, h, Nat.cast_smul_eq_nsmul]
    abel
  have h1 : EntriesLE b (lam ^ j * lam ^ j) ((ℓ : E) • X) := by
    rw [e]
    exact (entriesLE_one_add_pow_sub hj0 hj1 hgX ℓ).neg
  have h2 : lam ^ j * lam ^ j = ‖(ℓ : E)‖ * lam ^ (j + j - 1) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  rw [h2] at h1
  exact (h1.of_smul hℓ0).mono (pow_le_pow_of_le_one hlam0 hℓ1.le (by omega))

/-- An element congruent to `1` modulo `ℓ ^ 2` whose image has order dividing `ℓ` has
trivial image. -/
theorem eq_one_of_pow_eq_one (hℓ0 : (ℓ : E) ≠ 0) (hℓ1 : ‖(ℓ : E)‖ < 1) {g : G}
    (hg : g ∈ congruenceSet b ρ ‖(ℓ : E)‖ 2) (h : ρ g ^ ℓ = 1) : ρ g = 1 := by
  have hall : ∀ k, g ∈ congruenceSet b ρ ‖(ℓ : E)‖ (2 + k) := by
    intro k
    induction k with
    | zero => simpa using hg
    | succ k ih =>
      exact mem_congruenceSet_succ_of_pow_eq_one (j := 2 + k) hℓ0 hℓ1 (by omega) ih h
  exact eq_one_of_forall_mem_congruenceSet (norm_nonneg _) hℓ1 fun j =>
    congruenceSet_antitone (norm_nonneg _) hℓ1.le (by omega) (hall j)

end Congruence

section Coprime

variable {G : Type*} [Group G]

/-- In a decreasing sequence of subgroups `H j` in which `ℓ`-th powers raise the level from
`j ≥ 1` to `j + 1`, an element of `H 2` whose `m`-th power lies in `H j`, with `m` prime to
`ℓ`, lies in `H j`. -/
theorem mem_of_coprime_pow_mem {H : ℕ → Subgroup G} (hanti : ∀ j k, j ≤ k → H k ≤ H j)
    {ℓ : ℕ} (hpow : ∀ j, 1 ≤ j → ∀ g ∈ H j, g ^ ℓ ∈ H (j + 1))
    {g : G} (hg : g ∈ H 2) {m : ℕ} (hcop : Nat.Coprime ℓ m) {j : ℕ} (hgm : g ^ m ∈ H j) :
    g ∈ H j := by
  have hiter : ∀ c : ℕ, g ^ (ℓ ^ c) ∈ H (2 + c) := by
    intro c
    induction c with
    | zero => simpa using hg
    | succ c ih =>
      rw [pow_succ, pow_mul]
      exact hpow (2 + c) (by omega) _ ih
  have hgl : g ^ (ℓ ^ j) ∈ H j := hanti j (2 + j) (by omega) (hiter j)
  have hcop' : Nat.Coprime (ℓ ^ j) m := Nat.Coprime.pow_left j hcop
  have hb := Nat.gcd_eq_gcd_ab (ℓ ^ j) m
  rw [hcop'.gcd_eq_one, Nat.cast_one] at hb
  have h1 : (g ^ (ℓ ^ j)) ^ (Nat.gcdA (ℓ ^ j) m) =
      g ^ (((ℓ ^ j : ℕ) : ℤ) * Nat.gcdA (ℓ ^ j) m) := by
    rw [zpow_mul, zpow_natCast]
  have h2 : (g ^ m) ^ (Nat.gcdB (ℓ ^ j) m) = g ^ ((m : ℤ) * Nat.gcdB (ℓ ^ j) m) := by
    rw [zpow_mul, zpow_natCast]
  have e : g = (g ^ (ℓ ^ j)) ^ (Nat.gcdA (ℓ ^ j) m) * (g ^ m) ^ (Nat.gcdB (ℓ ^ j) m) := by
    rw [h1, h2, ← zpow_add, ← hb, zpow_one]
  rw [e]
  exact (H j).mul_mem ((H j).zpow_mem hgl _) ((H j).zpow_mem hgm _)

end Coprime


section Main

/-- **Finite image of inertia from a tame Frobenius structure.** Let `ρ` be a continuous
irreducible representation of a topological group `G` on a finite-dimensional vector space
over an algebraically closed ultrametric field `E`, where `ℓ` is a prime with
`0 < ‖(ℓ : E)‖ < 1` (that is, `(ℓ : E) ≠ 0` and `‖(ℓ : E)‖ < 1`). Suppose
every neighbourhood of `1` contains a normal subgroup of finite index, and `I` is a normal
subgroup with an element `φ` such that, for every neighbourhood `U` of `1`, some set `P`
contains the commutators of `I` and the elements `φ x φ⁻¹ x⁻ᑫ` (`x ∈ I`), and every element
of `P` has a `p`-power power in `U`, where `p` is prime to `ℓ` and `q ≥ 2`. Then `ρ(I)` is
finite. -/
theorem finite_image_of_tameFrobenius
    {G : Type*} [Group G] [TopologicalSpace G]
    {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] [IsAlgClosed E]
    {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {ℓ p q : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ p) (hq : 2 ≤ q)
    (hℓ0 : (ℓ : E) ≠ 0) (hℓ1 : ‖(ℓ : E)‖ < 1)
    (I : Subgroup G) [I.Normal] (φ : G)
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ (N : Set G) ⊆ U)
    (hTame : ∀ U ∈ 𝓝 (1 : G), ∃ P : Set G, (∀ x ∈ P, ∃ a : ℕ, x ^ p ^ a ∈ U) ∧
      (∀ x ∈ I, ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ P) ∧ (∀ x ∈ I, φ * x * φ⁻¹ * (x ^ q)⁻¹ ∈ P))
    (ρ : G →* Module.End E V)
    (hρ : @Continuous G (Module.End E V) _ (moduleTopology E (Module.End E V)) ρ)
    (hirr : ∀ W : Submodule E V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (ρ '' (I : Set G)).Finite := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine (Set.finite_singleton (1 : Module.End E V)).subset ?_
    rintro f -
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  let b := Module.finBasis E V
  have hlam0 : 0 < ‖(ℓ : E)‖ := norm_pos_iff.mpr hℓ0
  let H : ℕ → Subgroup G := congruenceSubgroup b ρ hlam0 hℓ1.le hρ hN
  have hanti : ∀ j k, j ≤ k → H k ≤ H j := fun j k hjk g hg =>
    congruenceSet_antitone (norm_nonneg _) hℓ1.le hjk hg
  have hpowℓ : ∀ j, 1 ≤ j → ∀ g ∈ H j, g ^ ℓ ∈ H (j + 1) := fun j hj g hg =>
    pow_mem_congruenceSet_succ hℓ1 hj hg
  have hone : ∀ g, (∀ j, g ∈ H j) → ρ g = 1 := fun g hg =>
    eq_one_of_forall_mem_congruenceSet (norm_nonneg _) hℓ1 hg
  have hker : ∀ g, ρ g = 1 → ∀ j, g ∈ H j := fun g hg j =>
    mem_congruenceSet_of_eq_one (norm_nonneg _) hg j
  have hcopmem : ∀ g ∈ H 2, ∀ m, Nat.Coprime ℓ m → ∀ j, g ^ m ∈ H j → g ∈ H j :=
    fun g hg m hm j hgm => mem_of_coprime_pow_mem hanti hpowℓ hg hm hgm
  obtain ⟨N, hNn, hNf, hNH⟩ := hN _ (congruenceSet_mem_nhds (b := b) hρ hlam0 2)
  have hN2 : ∀ g ∈ N, g ∈ H 2 := fun g hg => hNH hg
  let I' : Subgroup G := I ⊓ N
  have hI'n : I'.Normal := Subgroup.normal_inf_normal I N
  choose P hP using fun j => hTame _ (congruenceSet_mem_nhds (b := b) hρ hlam0 j)
  have hwild : ∀ x ∈ N, (∀ j, x ∈ P j) → ρ x = 1 := by
    intro x hxN hxP
    apply hone
    intro j
    obtain ⟨a, ha⟩ := (hP j).1 x (hxP j)
    exact hcopmem x (hN2 x hxN) (p ^ a) (Nat.Coprime.pow_right a hcop) j ha
  have hcomm : ∀ x ∈ I', ∀ y ∈ I', ρ x * ρ y = ρ y * ρ x := by
    intro x hx y hy
    have hc : ρ (x * y * x⁻¹ * y⁻¹) = 1 := by
      apply hwild
      · exact N.mul_mem (N.mul_mem (N.mul_mem hx.2 hy.2) (N.inv_mem hx.2)) (N.inv_mem hy.2)
      · exact fun j => (hP j).2.1 x hx.1 y hy.1
    have e : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    calc ρ x * ρ y = ρ (x * y) := (map_mul ρ x y).symm
      _ = ρ ((x * y * x⁻¹ * y⁻¹) * (y * x)) := by rw [← e]
      _ = ρ (x * y * x⁻¹ * y⁻¹) * ρ (y * x) := map_mul ρ _ _
      _ = ρ y * ρ x := by rw [hc, one_mul, map_mul]
  have hfrob : ∀ x ∈ I', ρ φ * ρ x * ρ φ⁻¹ = ρ x ^ q := by
    intro x hx
    have hd : ρ (φ * x * φ⁻¹ * (x ^ q)⁻¹) = 1 := by
      apply hwild
      · exact N.mul_mem (hNn.conj_mem x hx.2 φ) (N.inv_mem (N.pow_mem hx.2 q))
      · exact fun j => (hP j).2.2 x hx.1
    have e : φ * x * φ⁻¹ = (φ * x * φ⁻¹ * (x ^ q)⁻¹) * x ^ q := by group
    calc ρ φ * ρ x * ρ φ⁻¹ = ρ (φ * x * φ⁻¹) := by rw [map_mul, map_mul]
      _ = ρ ((φ * x * φ⁻¹ * (x ^ q)⁻¹) * x ^ q) := by rw [← e]
      _ = ρ x ^ q := by rw [map_mul, hd, one_mul, map_pow]
  have hunip : ∀ x ∈ I', ∃ m : ℕ, 0 < m ∧ ∀ μ : E, (ρ x ^ m).HasEigenvalue μ → μ = 1 := by
    intro x hx
    have hPQ : ρ φ * ρ φ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hQP : ρ φ⁻¹ * ρ φ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact exists_pow_eigenvalue_eq_one (ρ.toHomUnits x).isUnit hPQ hQP hq (hfrob x hx)
  let S : Set (Module.End E V) :=
    {f | ∃ x ∈ I', ∃ m : ℕ, f = ρ x ^ m ∧ ∀ μ : E, f.HasEigenvalue μ → μ = 1}
  have hScomm : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f := by
    rintro f ⟨x, hx, m, rfl, -⟩ g ⟨y, hy, n, rfl, -⟩
    exact (Commute.pow_pow (hcomm x hx y hy) m n).eq
  have hSeig : ∀ f ∈ S, ∀ μ : E, f.HasEigenvalue μ → μ = 1 := by
    rintro f ⟨x, -, m, -, h⟩
    exact h
  let W : Submodule E V :=
    { carrier := {v | ∀ f ∈ S, f v = v}
      add_mem' := fun {v w} hv hw f hf => by rw [map_add, hv f hf, hw f hf]
      zero_mem' := fun f _ => map_zero f
      smul_mem' := fun c v hv f hf => by rw [map_smul, hv f hf] }
  have hWinv : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := by
    intro g v hv f hf
    obtain ⟨x, hx, m, rfl, heig⟩ := hf
    have hx' : g⁻¹ * x * g ∈ I' := by simpa using hI'n.conj_mem x hx g⁻¹
    have hconj : (g⁻¹ * x * g) ^ m = g⁻¹ * x ^ m * g := by
      simpa using conj_pow (a := g⁻¹) (b := x) (i := m)
    have hPQ : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hQP : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e2 : ρ (g⁻¹ * x * g) ^ m = ρ g⁻¹ * ρ x ^ m * ρ g := by
      rw [← map_pow, hconj, map_mul, map_mul, map_pow]
    have hmem : ρ (g⁻¹ * x * g) ^ m ∈ S := by
      refine ⟨_, hx', m, rfl, fun μ hμ => heig μ ?_⟩
      rw [e2] at hμ
      exact hasEigenvalue_of_conj hPQ hQP hμ
    have key : ρ g * ρ (g⁻¹ * x * g) ^ m = ρ x ^ m * ρ g := by
      rw [e2, ← mul_assoc, ← mul_assoc, hQP, one_mul]
    have hfix := hv _ hmem
    calc (ρ x ^ m) (ρ g v) = (ρ x ^ m * ρ g) v := rfl
      _ = (ρ g * ρ (g⁻¹ * x * g) ^ m) v := by rw [key]
      _ = ρ g ((ρ (g⁻¹ * x * g) ^ m) v) := rfl
      _ = ρ g v := by rw [hfix]
  have hWne : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_common_fixed S hScomm hSeig
    intro hbot
    have hvW : v ∈ W := hv
    rw [hbot] at hvW
    exact hv0 ((Submodule.mem_bot E).mp hvW)
  have hWtop : W = ⊤ := (hirr W hWinv).resolve_left hWne
  have hfin : ∀ x ∈ I', ∃ m : ℕ, 0 < m ∧ ρ x ^ m = 1 := by
    intro x hx
    obtain ⟨m, hm, heig⟩ := hunip x hx
    refine ⟨m, hm, LinearMap.ext fun v => ?_⟩
    have hv : v ∈ W := hWtop ▸ Submodule.mem_top
    exact hv _ ⟨x, hx, m, rfl, heig⟩
  have htf : ∀ a : ℕ, ∀ z ∈ N, ρ z ^ (ℓ ^ a) = 1 → ρ z = 1 := by
    intro a
    induction a with
    | zero =>
      intro z _ h
      simpa using h
    | succ a ih =>
      intro z hz h
      have h1 : ρ (z ^ ℓ) = 1 := by
        refine ih (z ^ ℓ) (N.pow_mem hz ℓ) ?_
        rw [map_pow, ← pow_mul, ← pow_succ']
        exact h
      rw [map_pow] at h1
      exact eq_one_of_pow_eq_one hℓ0 hℓ1 (hN2 z hz) h1
  have htriv : ∀ x ∈ I', ρ x = 1 := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := hfin x hx
    obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.ne_one
    have hy2 : x ^ (ℓ ^ a) ∈ H 2 := hN2 _ (N.pow_mem hx.2 _)
    have hy : ρ (x ^ (ℓ ^ a)) = 1 := by
      apply hone
      intro j
      refine hcopmem _ hy2 m' ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm') j ?_
      apply hker
      rw [← pow_mul, map_pow, hxm]
    rw [map_pow] at hy
    exact htf a x hx.2 hy
  have hfactor : ∀ x ∈ I, ∀ y ∈ I, (x : G ⧸ N) = (y : G ⧸ N) → ρ x = ρ y := by
    intro x hx y hy hxy
    have hxyN : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have h1 := htriv (x⁻¹ * y) ⟨I.mul_mem (I.inv_mem hx) hy, hxyN⟩
    calc ρ x = ρ x * ρ (x⁻¹ * y) := by rw [h1, mul_one]
      _ = ρ y := by rw [← map_mul, mul_inv_cancel_left]
  have : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  refine Set.finite_coe_iff.mp (Finite.of_injective
    (fun f : ρ '' (I : Set G) => ((f.2.choose : G) : G ⧸ N)) ?_)
  rintro ⟨f, hf⟩ ⟨f', hf'⟩ h
  apply Subtype.ext
  change f = f'
  rw [← hf.choose_spec.2, ← hf'.choose_spec.2]
  exact hfactor _ hf.choose_spec.1 _ hf'.choose_spec.1 h

end Main


end Langlands.LadicMonodromy
