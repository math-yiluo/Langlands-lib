import Langlands.BushnellKutzko.StratumExistence
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof
import Langlands.BushnellKutzko.PureStratumApproximationNonsplitTransfer
import Langlands.Representation.Category.Basic

/-! # Fundamental strata in smooth representations of `GL_N(F)`

The positive-level part of Bushnell (1987), §3, Theorem 2′, namely Theorem 2′(ii) and its proof
(printed p. 197), for an arbitrary nonarchimedean local field `F` and an arbitrary complex
representation of `GL_N(F)`. For such a representation the minimum-level result assumes that some
congruence subgroup `U^{l+1}(𝔄)` fixes a nonzero vector and that no `U^1(𝔄)` fixes a nonzero
vector. The level-zero case, Theorem 2′(i), is not treated. The module also proves the
coprimality step of BK93 (8.1.5), printed p. 268, and the split/nonsplit dichotomy of BK93 (2.3.3),
printed p. 58.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  {W : Type*} [AddCommGroup W] [Module ℂ W]

local notation "End" => Module.End F (Fin n → F)
set_option quotPrecheck false in
local notation "toG" => (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).symm

namespace LatticeChain

/-- **A character at every level with a fixed vector** (Bushnell 1987, §3, the remark after
(3.3), printed p. 196, and the proof of Theorem 2′(ii), printed p. 197). Let `ψ` be an additive
character of `F` trivial on `𝔭_F` but not on `𝔬_F`, and let `m ≥ 1`. If a nonzero vector is
fixed by `U^{m+1}(𝔄(𝓛))`, then some nonzero vector transforms under `U^m(𝔄(𝓛))` by
`g ↦ ψ(tr(b(g - 1)))` for some `b ∈ 𝔓^{-m}(𝓛)`. -/
theorem exists_traceCharacter_eigenvector (𝓛 : LatticeChain 𝒪[F] F (Fin n → F))
    (ρ : Representation ℂ (GeneralLinear n F) W) (ψ : AddChar F ℂ)
    (hψ : ∀ c ∈ 𝓂[F], ψ (c : F) = 1) (hψ' : ∃ c : 𝒪[F], ψ (c : F) ≠ 1) {m : ℕ} (hm : 1 ≤ m)
    {w : W} (hw0 : w ≠ 0) (hwfix : ∀ u ∈ 𝓛.unitFiltration (m + 1), ρ (toG u) w = w) :
    ∃ b ∈ 𝓛.endFiltration (-(m : ℤ)), ∃ v : W, v ≠ 0 ∧
      ∀ u ∈ 𝓛.unitFiltration m, ρ (toG u) v = elementCharacter (traceCharacter ψ) b u • v := by
  classical
  let Wf : Submodule ℂ W :=
    { carrier := {v | ∀ u ∈ 𝓛.unitFiltration (m + 1), ρ (toG u) v = v}
      add_mem' := fun {a b} ha hb u hu => by
        simp only [map_add, ha u hu, hb u hu]
      zero_mem' := fun u _ => map_zero _
      smul_mem' := fun c a ha u hu => by
        simp only [map_smul, ha u hu] }
  have hWmem : ∀ v, v ∈ Wf ↔ ∀ u ∈ 𝓛.unitFiltration (m + 1), ρ (toG u) v = v :=
    fun v => Iff.rfl
  have hw : w ∈ Wf := hwfix
  have htoG_mul : ∀ u u' : (Module.End F (Fin n → F))ˣ, toG (u * u') = toG u * toG u' :=
    fun u u' => map_mul _ u u'
  -- congruent units act in the same way on `Wf`
  have hact : ∀ g h : (Module.End F (Fin n → F))ˣ,
      g ∈ 𝓛.unitFiltration 0 → h ∈ 𝓛.unitFiltration 0 →
      (h : Module.End F (Fin n → F)) - g ∈ 𝓛.endFiltration ((m : ℤ) + 1) →
      ∀ v ∈ Wf, ρ (toG h) v = ρ (toG g) v := by
    intro g h hg hh hgh v hv
    have h1 : g⁻¹ * h ∈ 𝓛.unitFiltration (m + 1) :=
      𝓛.inv_mul_mem_unitFiltration hg hh (by exact_mod_cast hgh)
    have h2 : toG h = toG g * toG (g⁻¹ * h) := by
      rw [← htoG_mul, mul_inv_cancel_left]
    rw [h2, map_mul, Module.End.mul_apply, (hWmem v).1 hv _ h1]
  -- `Wf` is stable under `U^0(𝔄)`
  have hstab : ∀ g ∈ 𝓛.unitFiltration 0, ∀ v ∈ Wf, ρ (toG g) v ∈ Wf := by
    intro g hg v hv
    rw [hWmem]
    intro t ht
    have h1 : g⁻¹ * t * g ∈ 𝓛.unitFiltration (m + 1) :=
      𝓛.inv_mul_mul_mem_unitFiltration hg ht
    have h2 : toG t * toG g = toG g * toG (g⁻¹ * t * g) := by
      rw [← htoG_mul, ← htoG_mul]
      group
    rw [← Module.End.mul_apply, ← map_mul, h2, map_mul, Module.End.mul_apply,
      (hWmem v).1 hv _ h1]
  -- residue coordinates of `U^m(𝔄) / U^{m+1}(𝔄)`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨r, β, hβ, -⟩ := LatticeChain.exists_basis_splits_both hϖ 𝓛 𝓛
  have : Fintype 𝓀[F] := Fintype.ofFinite _
  have hX : ∀ z, 𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration m := fun z =>
    LatticeChain.coordEnd_mem hϖ hβ m z
  have hunit : ∀ z : Fin r → Fin r → 𝓀[F], ∃ g ∈ 𝓛.unitFiltration m,
      (g : Module.End F (Fin n → F)) = 1 + 𝓛.coordEnd hϖ β m z :=
    fun z => 𝓛.exists_mem_unitFiltration hm (hX z)
  choose f hf hfv using hunit
  have hU0 : ∀ z, f z ∈ 𝓛.unitFiltration 0 := fun z =>
    𝓛.unitFiltration_antitone (Nat.zero_le m) (hf z)
  have h0 : ∀ v ∈ Wf, ρ (toG (f 0)) v = v := by
    intro v hv
    have h := hact 1 (f 0) (one_mem _) (hU0 0) (by
      rw [hfv, Units.val_one, add_sub_cancel_left]
      exact LatticeChain.coordEnd_zero_mem hϖ hβ m) v hv
    rw [h, map_one, map_one, Module.End.one_apply]
  have hmul : ∀ y z, ∀ v ∈ Wf, ρ (toG (f (y + z))) v = ρ (toG (f y)) (ρ (toG (f z)) v) := by
    intro y z v hv
    have hdiff : ((f y * f z : (Module.End F (Fin n → F))ˣ) : Module.End F (Fin n → F)) -
        f (y + z) ∈ 𝓛.endFiltration ((m : ℤ) + 1) := by
      have e : ((f y * f z : (Module.End F (Fin n → F))ˣ) : Module.End F (Fin n → F)) -
          f (y + z) =
          (𝓛.coordEnd hϖ β m y + 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m (y + z)) +
            𝓛.coordEnd hϖ β m y * 𝓛.coordEnd hϖ β m z := by
        rw [Units.val_mul, hfv, hfv, hfv]
        noncomm_ring
      rw [e]
      refine add_mem (LatticeChain.coordEnd_add_sub_mem hϖ hβ m y z) ?_
      exact 𝓛.endFiltration_antitone (by omega) (𝓛.mul_mem_endFiltration (hX y) (hX z))
    have h := hact (f (y + z)) (f y * f z) (hU0 _) (mul_mem (hU0 y) (hU0 z)) hdiff v hv
    rw [← h, htoG_mul, map_mul, Module.End.mul_apply]
  -- a common eigenvector
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_addChar_eigenvector (fun z => ρ (toG (f z))) Wf
    (fun z v hv => hstab _ (hU0 z) v hv) h0 hmul hw hw0
  have hχ' : ∀ z, ρ (toG (f z)) v = χ z • v := hχ
  have hχX : ∀ z z', 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m z' ∈
      𝓛.endFiltration ((m : ℤ) + 1) → χ z = χ z' := by
    intro z z' hzz
    have h := hact (f z') (f z) (hU0 _) (hU0 _)
      (by rw [hfv, hfv, add_sub_add_left_eq_sub]; exact hzz) v hv
    rw [hχ', hχ'] at h
    exact smul_left_injective ℂ hv0 h
  -- the character `θ` of `𝔓^m / 𝔓^{m+1}`
  have hz : ∀ x : Module.End F (Fin n → F), ∃ z : Fin r → Fin r → 𝓀[F],
      x ∈ 𝓛.endFiltration m → x - 𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration ((m : ℤ) + 1) := by
    intro x
    by_cases hx : x ∈ 𝓛.endFiltration m
    · obtain ⟨z, hz⟩ := LatticeChain.exists_sub_coordEnd_mem hϖ hβ hx
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Z hZ using hz
  obtain ⟨b, hb, hθ⟩ := 𝓛.exists_mem_endFiltration_forall_eq ψ hψ hψ' m (fun x => χ (Z x))
    (by
      intro x hx y hy
      have e : 𝓛.coordEnd hϖ β m (Z (x + y)) - 𝓛.coordEnd hϖ β m (Z x + Z y) =
          -((x + y) - 𝓛.coordEnd hϖ β m (Z (x + y))) + (x - 𝓛.coordEnd hϖ β m (Z x)) +
            (y - 𝓛.coordEnd hϖ β m (Z y)) + (𝓛.coordEnd hϖ β m (Z x) +
              𝓛.coordEnd hϖ β m (Z y) - 𝓛.coordEnd hϖ β m (Z x + Z y)) := by
        abel
      have hmem : 𝓛.coordEnd hϖ β m (Z (x + y)) - 𝓛.coordEnd hϖ β m (Z x + Z y) ∈
          𝓛.endFiltration ((m : ℤ) + 1) := by
        rw [e]
        exact add_mem (add_mem (add_mem (neg_mem (hZ _ (add_mem hx hy))) (hZ x hx)) (hZ y hy))
          (LatticeChain.coordEnd_add_sub_mem hϖ hβ m _ _)
      change χ (Z (x + y)) = χ (Z x) * χ (Z y)
      rw [hχX _ _ hmem, AddChar.map_add_eq_mul])
    (by
      intro x hx
      have hxm : x ∈ 𝓛.endFiltration m := 𝓛.endFiltration_antitone (by omega) hx
      have hmem : 𝓛.coordEnd hϖ β m (Z x) - 𝓛.coordEnd hϖ β m 0 ∈
          𝓛.endFiltration ((m : ℤ) + 1) := by
        have e : 𝓛.coordEnd hϖ β m (Z x) - 𝓛.coordEnd hϖ β m 0 =
            -(x - 𝓛.coordEnd hϖ β m (Z x)) + x - 𝓛.coordEnd hϖ β m 0 := by
          abel
        rw [e]
        exact sub_mem (add_mem (neg_mem (hZ x hxm)) hx) (LatticeChain.coordEnd_zero_mem hϖ hβ m)
      change χ (Z x) = 1
      rw [hχX _ _ hmem, AddChar.map_zero_eq_one])
  refine ⟨b, hb, v, hv0, fun u hu => ?_⟩
  have hx : (u : Module.End F (Fin n → F)) - 1 ∈ 𝓛.endFiltration m := hu.2.2
  have h := hact (f (Z ((u : Module.End F (Fin n → F)) - 1))) u (hU0 _)
    (𝓛.unitFiltration_antitone (Nat.zero_le m) hu) (by
      rw [hfv, ← sub_sub]
      exact hZ _ hx) v hv
  rw [h, hχ', elementCharacter_apply, traceCharacter_apply, ← hθ _ hx]


/-- **A stratum at a minimal level is fundamental** (Bushnell 1987, §3, Theorem 2′(ii) and its
proof, printed p. 197). Let `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)` and let `v ≠ 0` transform under `U^m(𝔄(𝓛))` by
`g ↦ ψ(tr(b(g - 1)))`. Suppose that `m / e(𝓛) ≤ l / e(𝓜)` whenever `U^{l+1}(𝔄(𝓜))` fixes a
nonzero vector. Then `b + y` is not nilpotent for any `y ∈ 𝔓^{1-m}(𝓛)`. -/
theorem not_isNilpotent_add_of_minimal (𝓛 : LatticeChain 𝒪[F] F (Fin n → F))
    (ρ : Representation ℂ (GeneralLinear n F) W) (ψ : AddChar F ℂ)
    (hψ : ∀ c ∈ 𝓂[F], ψ (c : F) = 1) {m : ℕ} (hm : 1 ≤ m)
    {b : Module.End F (Fin n → F)} (hb : b ∈ 𝓛.endFiltration (-(m : ℤ))) {v : W} (hv0 : v ≠ 0)
    (hv : ∀ u ∈ 𝓛.unitFiltration m, ρ (toG u) v = elementCharacter (traceCharacter ψ) b u • v)
    (hmin : ∀ (𝓜 : LatticeChain 𝒪[F] F (Fin n → F)) (l : ℕ) (w : W), w ≠ 0 →
      (∀ u ∈ 𝓜.unitFiltration (l + 1), ρ (toG u) w = w) → m * 𝓜.period ≤ l * 𝓛.period) :
    ∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y) := by
  intro y hy hnil
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨𝓜, l, hlt, hbM, hle⟩ := 𝓛.exists_latticeChain_of_isNilpotent_add hϖ (m := m)
    (by exact_mod_cast hm) hb hy hnil
  have hU : 𝓜.unitFiltration (l + 1) ≤ 𝓛.unitFiltration m :=
    𝓛.unitFiltration_le_of_endFiltration_le 𝓜 hm (by exact_mod_cast hle)
  have h := hmin 𝓜 l v hv0 (fun u hu => by
    rw [hv u (hU hu)]
    have h1 := 𝓜.mul_mem_endFiltration hbM hu.2.2
    rw [show -(l : ℤ) + ((l + 1 : ℕ) : ℤ) = 1 by push_cast; ring] at h1
    have h2 := 𝓜.addChar_trace_eq_one_of_mem_one hϖ ψ hψ h1
    rw [elementCharacter_apply, traceCharacter_apply, h2, one_smul])
  have h' : ((m * 𝓜.period : ℕ) : ℤ) ≤ ((l * 𝓛.period : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  omega

end LatticeChain

/-! ### Coarser lattice chains -/

namespace LatticeChain

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K] {V : Type*}
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- The lattice chain `i ↦ L_{d i}` formed by every `d`-th lattice of `𝓛`, for a divisor `d` of
the period `e(𝓛)`. Its period is `e(𝓛) / d` (`period_stride`). -/
def stride (𝓛 : LatticeChain O K V) (d : ℕ) (hd : 0 < d) (hdvd : d ∣ 𝓛.period) :
    LatticeChain O K V where
  lattice i := 𝓛.lattice (d * i)
  isLattice i := 𝓛.isLattice _
  lattice_succ_lt i := 𝓛.strictAnti (by
    have : (0 : ℤ) < d := by exact_mod_cast hd
    linarith)
  exists_period := ⟨𝓛.period / d, Nat.div_pos (Nat.le_of_dvd 𝓛.period_pos hdvd) hd, fun i => by
    have h : (d : ℤ) * (i + ((𝓛.period / d : ℕ) : ℤ)) = d * i + 𝓛.period := by
      rw [mul_add]
      congr 1
      exact_mod_cast Nat.mul_div_cancel' hdvd
    change 𝓛.lattice _ = _ • 𝓛.lattice _
    rw [h]
    exact 𝓛.lattice_add_period _⟩

theorem stride_lattice (𝓛 : LatticeChain O K V) (d : ℕ) (hd : 0 < d) (hdvd : d ∣ 𝓛.period)
    (i : ℤ) : (𝓛.stride d hd hdvd).lattice i = 𝓛.lattice (d * i) :=
  rfl

theorem period_stride (𝓛 : LatticeChain O K V) (d : ℕ) (hd : 0 < d) (hdvd : d ∣ 𝓛.period) :
    (𝓛.stride d hd hdvd).period = 𝓛.period / d := by
  refine ((𝓛.stride d hd hdvd).period_unique fun i => ?_).symm
  have h : (d : ℤ) * (i + ((𝓛.period / d : ℕ) : ℤ)) = d * i + 𝓛.period := by
    rw [mul_add]
    congr 1
    exact_mod_cast Nat.mul_div_cancel' hdvd
  rw [stride_lattice, stride_lattice, h]
  exact 𝓛.lattice_add_period _

/-- `𝔓^{k+1}` of the chain `i ↦ L_{d i}` lies in `𝔓^{dk+1}(𝓛)`. -/
theorem endFiltration_stride_le (𝓛 : LatticeChain O K V) (d : ℕ) (hd : 0 < d)
    (hdvd : d ∣ 𝓛.period) (k : ℤ) :
    (𝓛.stride d hd hdvd).endFiltration (k + 1) ≤ 𝓛.endFiltration (d * k + 1) := by
  intro x hx j v hv
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  set q := j / (d : ℤ) with hq
  have h1 : (d : ℤ) * q + j % d = j := Int.mul_ediv_add_emod j d
  have h2 : 0 ≤ j % (d : ℤ) := Int.emod_nonneg j hd'.ne'
  have h3 : j % (d : ℤ) < d := Int.emod_lt_of_pos j hd'
  have hvq : v ∈ (𝓛.stride d hd hdvd).lattice q := 𝓛.antitone (by
    change (d : ℤ) * q ≤ j
    linarith) hv
  have h := hx q v hvq
  rw [stride_lattice] at h
  exact 𝓛.antitone (by nlinarith) h

end LatticeChain

/-! ### A minimal level with coprime period -/

/-- **A pair of minimal normalized level** (Bushnell 1987, §3, Theorem 2′(ii),
printed p. 197; BK93 (8.1.5), printed p. 268).
Suppose that `U^{l+1}(𝔄(𝓛))` fixes a nonzero vector of `ρ` for some lattice chain `𝓛` in `F^N`
and some `l`, but that no `U^1(𝔄(𝓛))` fixes a nonzero vector. Then there is a lattice chain `𝓛`
and `m ≥ 1` coprime to `e(𝓛)` such that `U^{m+1}(𝔄(𝓛))` fixes a nonzero vector and
`m / e(𝓛) ≤ l / e(𝓜)` whenever `U^{l+1}(𝔄(𝓜))` fixes a nonzero vector. -/
theorem exists_minimal_fixed_level (ρ : Representation ℂ (GeneralLinear n F) W)
    (hex : ∃ (𝓛 : LatticeChain 𝒪[F] F (Fin n → F)) (l : ℕ) (w : W), w ≠ 0 ∧
      ∀ u ∈ 𝓛.unitFiltration (l + 1), ρ (toG u) w = w)
    (hnone : ∀ (𝓛 : LatticeChain 𝒪[F] F (Fin n → F)) (w : W), w ≠ 0 →
      ¬ ∀ u ∈ 𝓛.unitFiltration 1, ρ (toG u) w = w) :
    ∃ (𝓛 : LatticeChain 𝒪[F] F (Fin n → F)) (m : ℕ) (w : W), 1 ≤ m ∧
      Nat.Coprime m 𝓛.period ∧ w ≠ 0 ∧ (∀ u ∈ 𝓛.unitFiltration (m + 1), ρ (toG u) w = w) ∧
      ∀ (𝓜 : LatticeChain 𝒪[F] F (Fin n → F)) (l : ℕ) (w' : W), w' ≠ 0 →
        (∀ u ∈ 𝓜.unitFiltration (l + 1), ρ (toG u) w' = w') → m * 𝓜.period ≤ l * 𝓛.period := by
  classical
  -- every period divides `N!`
  have hdvd : ∀ 𝓛 : LatticeChain 𝒪[F] F (Fin n → F), 𝓛.period ∣ n.factorial := fun 𝓛 =>
    Nat.dvd_factorial 𝓛.period_pos (by simpa using 𝓛.period_le_card)
  let P : ℕ → Prop := fun k => ∃ (𝓛 : LatticeChain 𝒪[F] F (Fin n → F)) (l : ℕ) (w : W),
    w ≠ 0 ∧ (∀ u ∈ 𝓛.unitFiltration (l + 1), ρ (toG u) w = w) ∧
      l * (n.factorial / 𝓛.period) = k
  have hP : ∃ k, P k := by
    obtain ⟨𝓛, l, w, hw0, hw⟩ := hex
    exact ⟨_, 𝓛, l, w, hw0, hw, rfl⟩
  obtain ⟨𝓛, m, w, hw0, hw, hk⟩ := Nat.find_spec hP
  -- minimality in the form `m e(𝓜) ≤ l e(𝓛)`
  have hmin : ∀ (𝓜 : LatticeChain 𝒪[F] F (Fin n → F)) (l : ℕ) (w' : W), w' ≠ 0 →
      (∀ u ∈ 𝓜.unitFiltration (l + 1), ρ (toG u) w' = w') → m * 𝓜.period ≤ l * 𝓛.period := by
    intro 𝓜 l w' hw'0 hw'
    have h := Nat.find_min' hP ⟨𝓜, l, w', hw'0, hw', rfl⟩
    rw [← hk] at h
    obtain ⟨a, ha⟩ := hdvd 𝓛
    obtain ⟨c, hc⟩ := hdvd 𝓜
    have hL := 𝓛.period_pos
    have hM := 𝓜.period_pos
    have ha' : n.factorial / 𝓛.period = a := by
      rw [ha, Nat.mul_div_cancel_left _ hL]
    have hc' : n.factorial / 𝓜.period = c := by
      rw [hc, Nat.mul_div_cancel_left _ hM]
    rw [ha', hc'] at h
    have hac : 𝓛.period * a = 𝓜.period * c := ha.symm.trans hc
    have h2 : m * 𝓜.period * (𝓛.period * a) ≤ l * 𝓛.period * (𝓛.period * a) := by
      calc m * 𝓜.period * (𝓛.period * a) = m * a * (𝓛.period * 𝓜.period) := by ring
        _ ≤ l * c * (𝓛.period * 𝓜.period) := Nat.mul_le_mul_right _ h
        _ = l * 𝓛.period * (𝓜.period * c) := by ring
        _ = l * 𝓛.period * (𝓛.period * a) := by rw [hac]
    have hpos : 0 < 𝓛.period * a := by
      rw [← ha]
      exact Nat.factorial_pos n
    exact Nat.le_of_mul_le_mul_right h2 hpos
  -- the level is positive
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exact absurd hw (hnone 𝓛 w hw0)
    · exact h0
  -- pass to the chain `i ↦ L_{d i}` with `d = gcd(m, e(𝓛))`
  set d := Nat.gcd m 𝓛.period with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hm1
  have hde : d ∣ 𝓛.period := Nat.gcd_dvd_right _ _
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  set 𝓛' := 𝓛.stride d hdpos hde with h𝓛'
  have hper : 𝓛'.period = 𝓛.period / d := 𝓛.period_stride d hdpos hde
  have hm' : m / d * d = m := Nat.div_mul_cancel hdm
  have he' : 𝓛.period / d * d = 𝓛.period := Nat.div_mul_cancel hde
  refine ⟨𝓛', m / d, w, ?_, ?_, hw0, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hm1 hdm) hdpos
  · rw [hper]
    exact Nat.coprime_div_gcd_div_gcd hdpos
  · have hle : 𝓛'.endFiltration (((m / d : ℕ) : ℤ) + 1) ≤
        𝓛.endFiltration (((m + 1 : ℕ) : ℤ)) := by
      have h := 𝓛.endFiltration_stride_le d hdpos hde ((m / d : ℕ) : ℤ)
      have e : (d : ℤ) * ((m / d : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by
        rw [mul_comm]
        exact_mod_cast congrArg (· + 1) hm'
      rwa [e] at h
    have hU := 𝓛.unitFiltration_le_of_endFiltration_le 𝓛' (Nat.le_add_left 1 m)
      (by exact_mod_cast hle)
    exact fun u hu => hw u (hU hu)
  · intro 𝓜 l w' hw'0 hw'
    have h := hmin 𝓜 l w' hw'0 hw'
    rw [hper]
    refine Nat.le_of_mul_le_mul_right (?_ : _ * d ≤ _ * d) hdpos
    calc m / d * 𝓜.period * d = m / d * d * 𝓜.period := by ring
      _ = m * 𝓜.period := by rw [hm']
      _ ≤ l * 𝓛.period := h
      _ = l * (𝓛.period / d * d) := by rw [he']
      _ = l * (𝓛.period / d) * d := by ring

/-! ### Split and nonsplit fundamental strata -/

namespace Stratum

/-- A fundamental stratum over `𝔬_F` that is not split is nonsplit (BK93 (2.3.3), printed
p. 58): the polynomial `φ_b`, monic of degree `dim_F V`, has a single monic irreducible factor. -/
theorem isNonsplit_of_not_isSplit {V : Type*} [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (hS : S.IsFundamental) (hns : ¬ S.IsSplit) : S.IsNonsplit := by
  classical
  have := S.chain.finiteDimensional
  have := S.chain.nontrivialSpace
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let π : RingPrimeElement 𝒪[F] :=
    ⟨ϖ, hϖ.ne_zero, by rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  have hmax : (Ring.jacobson 𝒪[F]).IsMaximal := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal _
  let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _
  have hinj : Function.Injective (algebraMap 𝒪[F] F) := Subtype.val_injective
  have hmon := PureApproximation.reduceIntegralPolynomial_monic (O := 𝒪[F]) hinj
    (LinearMap.charpoly_monic (S.fundamentalElement π))
  have hφmon : (S.fundamentalPolynomial π).Monic := hmon.1
  have hφdeg : 0 < (S.fundamentalPolynomial π).natDegree := by
    unfold Stratum.fundamentalPolynomial
    rw [hmon.2, LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  obtain ⟨p, m, hpm, hpi, hm, hφp⟩ :=
    PureApproximation.exists_eq_pow_of_not_two_factors hφmon hφdeg
      (fun ⟨p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩ =>
        hns ⟨hS, π, p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩)
  exact ⟨hS, π, p, m, hpm, hpi, hm, hφp⟩

end Stratum


end Langlands.BushnellKutzko
