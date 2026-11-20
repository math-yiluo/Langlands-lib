import Langlands.BushnellKutzko.RelativeFiltrationInversion
import Langlands.BushnellKutzko.LatticeChainShifts
import Langlands.BushnellKutzko.SplittingBasis

/-! # Relative splitting bases and the attached diagonal embedding

For a field `L` acting on `V` whose units normalize a lattice chain, a relative splitting basis
`w` of `V` over `L` gives matrix units `ε_{jl}` and the diagonal embedding
`Δ : End_F(L) → End_F(V)`, `Δ(y)(Σ c_j w_j) = Σ y(c_j) w_j`.
-/

open ValuativeRel
open scoped BigOperators

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uL

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {L : Type uL} [Field L] [Algebra F L] [Module L V] [IsScalarTower F L V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "Lat" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

section Splitting

theorem refinement_scalar_lattice_shift
    (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer) {c : L} (hc : c ≠ 0) :
    ∃ d : ℤ, ∀ (i : ℤ) (v : V), c • v ∈ Lat (i + d) ↔ v ∈ Lat i := by
  let u := Units.mk0 c hc
  let g : 𝓛.stabilizer := ⟨subfieldUnits F L V u, hnormal u⟩
  refine ⟨𝓛.stabilizerValuation g, fun i v => ?_⟩
  rw [← 𝓛.map_lattice_stabilizer g i, Submodule.mem_map]
  change (∃ w ∈ Lat i, c • w = c • v) ↔ v ∈ Lat i
  exact ⟨fun ⟨w, hw, heq⟩ => (smul_right_injective V hc heq) ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]}

theorem refinement_lattice_maximal_coset_rep (hϖ : Irreducible ϖ)
    (U : Submodule L V) {x : V} (hx : x ∉ U) :
    ∃ w : V, w - x ∈ U ∧ ∀ i : ℤ, (∃ y ∈ Lat i, y - x ∈ U) → w ∈ Lat i := by
  let W := U.restrictScalars F
  let q := W.mkQ
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr W.mkQ_surjective)
  let f := s.comp q
  have hker (v : V) : f v = 0 ↔ v ∈ U := by
    have hq : q v = 0 ↔ v ∈ U := by
      change v ∈ W.mkQ.ker ↔ v ∈ W
      rw [Submodule.ker_mkQ]
    constructor
    · intro heq
      apply hq.mp
      have h := LinearMap.congr_fun hs (q v)
      change q (f v) = q v at h
      rw [heq, map_zero] at h
      exact h.symm
    · intro hv
      change s (q v) = 0
      rw [hq.mpr hv, map_zero]
  obtain ⟨t, ht⟩ := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ f 0
  let p := -(t : ℤ) * 𝓛.period
  have hfp : f ∈ P p := by
    apply (𝓛.uniformizer_pow_end_mem_iff hϖ t p f).mp
    simpa only [p, neg_mul, neg_add_cancel] using ht
  have hsep : ∃ i : ℤ, f x ∉ Lat i := by
    by_contra! h
    exact hx ((hker x).mp (𝓛.lattice_eq_zero_of_forall h))
  obtain ⟨i, hi⟩ := hsep
  let C : Set ℤ := {j | ∃ y ∈ Lat j, y - x ∈ U}
  obtain ⟨j, hj⟩ := 𝓛.exists_lattice_depth hϖ x
  have hne : C.Nonempty := ⟨j, x, hj, by simp⟩
  have hbdd : BddAbove C := by
    refine ⟨i - p, fun k hk => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hk
    have hfy : f y = f x := by
      have h := (hker (y - x)).mpr hyx
      rwa [map_sub, sub_eq_zero] at h
    have hfL := 𝓛.mem_endFiltration.mp hfp k y hy
    rw [hfy] at hfL
    by_contra! hk
    exact hi (𝓛.antitone (show i ≤ k + p by omega) hfL)
  obtain ⟨w, hw, hwx⟩ := Int.csSup_mem hne hbdd
  exact ⟨w, hwx, fun j hj => 𝓛.antitone (le_csSup hbdd hj) hw⟩

end LocalField

theorem refinement_coset_rep_smul_mem
    (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer)
    (U : Submodule L V) {w : V} (hw : ∀ j : ℤ, (∃ y ∈ Lat j, y - w ∈ U) → w ∈ Lat j)
    {u : V} (hu : u ∈ U) (c : L) (i : ℤ) (h : u + c • w ∈ Lat i) : c • w ∈ Lat i := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨d, hd⟩ := refinement_scalar_lattice_shift 𝓛 hnormal hc
  let y := c⁻¹ • u + w
  have hy : c • y = u + c • w := by rw [smul_add, smul_inv_smul₀ hc]
  have hyL : y ∈ Lat (i - d) := (hd (i - d) y).mp (by rwa [hy, sub_add_cancel])
  have hyU : y - w ∈ U := by
    change c⁻¹ • u + w - w ∈ U
    rw [add_sub_cancel_right]
    exact U.smul_mem _ hu
  have hcw := (hd (i - d) w).mpr (hw _ ⟨y, hyL, hyU⟩)
  rwa [sub_add_cancel] at hcw

/-- A family `w` splits the chain relative to `L`: every lattice containing a combination
`Σ c_j w_j` contains each term `c_j w_j`. -/
def RelSplits {n : ℕ} (w : Fin n → V) : Prop :=
  ∀ (i : ℤ) (c : Fin n → L), (∑ j, c j • w j) ∈ Lat i → ∀ j, c j • w j ∈ Lat i

theorem relSplits_finCons
    (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer)
    {n : ℕ} {w : Fin n → V} (hw : RelSplits (L := L) 𝓛 w) {v : V}
    (hv : ∀ j : ℤ, (∃ y ∈ Lat j, y - v ∈ Submodule.span L (Set.range w)) → v ∈ Lat j) :
    RelSplits (L := L) 𝓛 (Fin.cons v w) := by
  intro i c h j
  let u := ∑ r : Fin n, c r.succ • w r
  have hu : u ∈ Submodule.span L (Set.range w) := Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self r))
  have hsum : u + c 0 • v ∈ Lat i := by
    rw [Fin.sum_univ_succ] at h
    simpa only [u, Fin.cons_zero, Fin.cons_succ, add_comm] using h
  have hl := refinement_coset_rep_smul_mem 𝓛 hnormal _ hv hu (c 0) i hsum
  have huL : u ∈ Lat i := by
    have hs := (Lat i).sub_mem hsum hl
    rwa [add_sub_cancel_right] at hs
  refine Fin.cases ?_ (fun r => ?_) j
  · simpa only [Fin.cons_zero] using hl
  · simpa only [Fin.cons_succ] using hw i (fun r => c r.succ) huL r

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]}

/-- A normalized field has a relative splitting basis (as in BK93 (1.2.8)). -/
theorem exists_relSplits_basis [FiniteDimensional F V] (hϖ : Irreducible ϖ)
    (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) L V), RelSplits (L := L) 𝓛 w := by
  let : FiniteDimensional L V := Module.Finite.of_restrictScalars_finite F L V
  let S : Set ℕ := {n | ∃ w : Fin n → V, LinearIndependent L w ∧ RelSplits (L := L) 𝓛 w}
  have hne : S.Nonempty := by
    refine ⟨0, Fin.elim0, linearIndependent_empty_type, fun _ _ _ j => Fin.elim0 j⟩
  have hbound (n : ℕ) (hn : n ∈ S) : n ≤ Module.finrank L V := by
    obtain ⟨w, hw, _⟩ := hn
    simpa only [Fintype.card_fin] using hw.fintype_card_le_finrank
  have hfin : S.Finite := (Set.finite_le_nat (Module.finrank L V)).subset fun n hn => hbound n hn
  have hmax := hne.isGreatest_csSup hfin
  obtain ⟨w, hw, hsplit⟩ := hmax.1
  let U := Submodule.span L (Set.range w)
  have hU : U = ⊤ := by
    by_contra hne
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    obtain ⟨v, hvU, hv⟩ := refinement_lattice_maximal_coset_rep 𝓛 hϖ U hx
    have hv' : v ∉ U := fun hv => hx (sub_sub_cancel v x ▸ U.sub_mem hv hvU)
    have hvmax (i : ℤ) (hi : ∃ y ∈ Lat i, y - v ∈ U) : v ∈ Lat i := by
      obtain ⟨y, hy, hyv⟩ := hi
      exact hv i ⟨y, hy, sub_add_sub_cancel y v x ▸ U.add_mem hyv hvU⟩
    have hs : sSup S + 1 ∈ S := ⟨Fin.cons v w, hw.finCons hv',
      relSplits_finCons 𝓛 hnormal hsplit hvmax⟩
    exact (Nat.not_succ_le_self _) (hmax.2 hs)
  let basis := Module.Basis.mk hw hU.ge
  refine ⟨sSup S, basis, ?_⟩
  simpa only [basis, Module.Basis.coe_mk] using hsplit

end LocalField

end Splitting

/-! ### Matrix units and the diagonal embedding -/

section Diagonal

variable {n : ℕ} (w : Module.Basis (Fin n) L V)

variable (F) in
/-- The inclusion `a ↦ a • w_j` of the `j`-th line. -/
def lineIncl (j : Fin n) : L →ₗ[F] V :=
  (LinearMap.toSpanSingleton L V (w j)).restrictScalars F

variable (F) in
/-- The `j`-th coordinate with respect to `w`. -/
def lineProj (j : Fin n) : V →ₗ[F] L :=
  (w.coord j).restrictScalars F

@[simp]
theorem lineIncl_apply (j : Fin n) (a : L) : lineIncl F w j a = a • w j := rfl

@[simp]
theorem lineProj_apply (j : Fin n) (v : V) : lineProj F w j v = w.repr v j := rfl

theorem repr_smul_basis (j k : Fin n) (a : L) :
    w.repr (a • w k) j = if k = j then a else 0 := by
  rw [map_smul, w.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

variable (F) in
/-- The matrix unit `ε_{jl}`, `Σ c_i w_i ↦ c_l w_j`. -/
def matUnit (j l : Fin n) : Module.End F V := lineIncl F w j ∘ₗ lineProj F w l

@[simp]
theorem matUnit_apply (j l : Fin n) (v : V) : matUnit F w j l v = w.repr v l • w j := rfl

theorem matUnit_mul_matUnit (j l k m : Fin n) :
    matUnit F w j l * matUnit F w k m = if l = k then matUnit F w j m else 0 := by
  ext v
  rw [Module.End.mul_apply, matUnit_apply, matUnit_apply, repr_smul_basis]
  by_cases h : l = k
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h, zero_smul, LinearMap.zero_apply]

theorem sum_matUnit_self : ∑ j, matUnit F w j j = 1 := by
  ext v
  rw [LinearMap.sum_apply]
  simpa using w.sum_repr v

variable (F) in
/-- The diagonal embedding `Δ(y) = Σ_j ι_j ∘ y ∘ π_j` as a linear map. -/
def diagonalLinear : Module.End F L →ₗ[F] Module.End F V where
  toFun y := ∑ j, lineIncl F w j ∘ₗ y ∘ₗ lineProj F w j
  map_add' y y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c y := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

theorem diagonalLinear_apply (y : Module.End F L) (v : V) :
    diagonalLinear F w y v = ∑ j, y (w.repr v j) • w j := by
  change (∑ j, lineIncl F w j ∘ₗ y ∘ₗ lineProj F w j) v = _
  rw [LinearMap.sum_apply]
  rfl

theorem repr_diagonalLinear (y : Module.End F L) (v : V) (j : Fin n) :
    w.repr (diagonalLinear F w y v) j = y (w.repr v j) := by
  rw [diagonalLinear_apply, w.repr_sum_self (fun j => y (w.repr v j))]

variable (F) in
/-- The diagonal embedding `Δ : End_F(L) → End_F(V)`. -/
def diagonal : Module.End F L →ₐ[F] Module.End F V :=
  AlgHom.ofLinearMap (diagonalLinear F w)
    (by
      ext v
      rw [diagonalLinear_apply]
      simpa using w.sum_repr v)
    (by
      intro y y'
      ext v
      rw [Module.End.mul_apply, diagonalLinear_apply, diagonalLinear_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [repr_diagonalLinear, Module.End.mul_apply])

theorem diagonal_apply (y : Module.End F L) (v : V) :
    diagonal F w y v = ∑ j, y (w.repr v j) • w j :=
  diagonalLinear_apply w y v

theorem repr_diagonal (y : Module.End F L) (v : V) (j : Fin n) :
    w.repr (diagonal F w y v) j = y (w.repr v j) :=
  repr_diagonalLinear w y v j

theorem diagonal_smul_basis (y : Module.End F L) (a : L) (l : Fin n) :
    diagonal F w y (a • w l) = y a • w l := by
  rw [diagonal_apply]
  rw [Finset.sum_eq_single l]
  · rw [repr_smul_basis, if_pos rfl]
  · intro j _ hj
    rw [repr_smul_basis, if_neg (Ne.symm hj), map_zero, zero_smul]
  · simp

theorem diagonal_commute_matUnit (y : Module.End F L) (j l : Fin n) :
    diagonal F w y * matUnit F w j l = matUnit F w j l * diagonal F w y := by
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, matUnit_apply, matUnit_apply,
    diagonal_smul_basis, repr_diagonal]

theorem diagonal_mulLeft (a : L) :
    diagonal F w (LinearMap.mulLeft F a) = subfieldEmbedding F L V a := by
  ext v
  rw [diagonal_apply, subfieldEmbedding_apply]
  conv_rhs => rw [← w.sum_repr v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.mulLeft_apply, smul_smul]

variable (F) in
/-- Compression to the `l`-th line: `π_l ∘ z ∘ ι_l`. -/
def compress (l : Fin n) (z : Module.End F V) : Module.End F L :=
  lineProj F w l ∘ₗ z ∘ₗ lineIncl F w l

theorem compress_apply (l : Fin n) (z : Module.End F V) (a : L) :
    compress F w l z a = w.repr (z (a • w l)) l := rfl

theorem compress_diagonal (l : Fin n) (y : Module.End F L) :
    compress F w l (diagonal F w y) = y := by
  ext a
  rw [compress_apply, diagonal_smul_basis, repr_smul_basis, if_pos rfl]

theorem compress_add (l : Fin n) (z z' : Module.End F V) :
    compress F w l (z + z') = compress F w l z + compress F w l z' := by
  ext a
  simp [compress_apply]

theorem compress_sub (l : Fin n) (z z' : Module.End F V) :
    compress F w l (z - z') = compress F w l z - compress F w l z' := by
  ext a
  simp [compress_apply]

/-- An `L`-linear endomorphism compresses to multiplication by its `(l,l)` entry. -/
theorem compress_of_commute (l : Fin n) {z : Module.End F V}
    (hz : ∀ a : L, z * subfieldEmbedding F L V a = subfieldEmbedding F L V a * z) :
    compress F w l z = LinearMap.mulLeft F (w.repr (z (w l)) l) := by
  ext a
  rw [compress_apply, LinearMap.mulLeft_apply]
  have h := LinearMap.congr_fun (hz a) (w l)
  rw [Module.End.mul_apply, Module.End.mul_apply, subfieldEmbedding_apply,
    subfieldEmbedding_apply] at h
  rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- The sandwich `σ_l(z) = Σ_j ε_{jl} z ε_{lj}` equals `Δ(π_l z ι_l)`. -/
theorem diagonal_compress (l : Fin n) (z : Module.End F V) :
    diagonal F w (compress F w l z) = ∑ j, matUnit F w j l * z * matUnit F w l j := by
  ext v
  rw [diagonal_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, matUnit_apply, matUnit_apply,
    compress_apply]

/-- An element commuting with every matrix unit is the diagonal of its compression. -/
theorem diagonal_compress_of_commute (l : Fin n) {z : Module.End F V}
    (hz : ∀ j k, z * matUnit F w j k = matUnit F w j k * z) :
    diagonal F w (compress F w l z) = z := by
  rw [diagonal_compress]
  have h (j : Fin n) : matUnit F w j l * z * matUnit F w l j = z * matUnit F w j j := by
    rw [← hz j l, mul_assoc, matUnit_mul_matUnit, if_pos rfl]
  simp_rw [h, ← Finset.mul_sum, sum_matUnit_self, mul_one]

theorem subfieldEmbedding_commute_matUnit (a : L) (j l : Fin n) :
    subfieldEmbedding F L V a * matUnit F w j l = matUnit F w j l * subfieldEmbedding F L V a := by
  rw [← diagonal_mulLeft, diagonal_commute_matUnit]

theorem compress_injective_of_commute (l : Fin n) {z z' : Module.End F V}
    (hz : ∀ j k, z * matUnit F w j k = matUnit F w j k * z)
    (hz' : ∀ j k, z' * matUnit F w j k = matUnit F w j k * z')
    (h : compress F w l z = compress F w l z') : z = z' := by
  rw [← diagonal_compress_of_commute w l hz, ← diagonal_compress_of_commute w l hz', h]

theorem diagonal_injective (l : Fin n) : Function.Injective (diagonal F w) := by
  intro y y' h
  rw [← compress_diagonal w l y, ← compress_diagonal w l y', h]

end Diagonal

/-! ### Filtration properties of the matrix units -/

section Filtration

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
  (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer)
  {n : ℕ} {w : Module.Basis (Fin n) L V} (hw : RelSplits (L := L) 𝓛 w)

include hw in
theorem repr_smul_mem {v : V} {i : ℤ} (hv : v ∈ Lat i) (j : Fin n) :
    w.repr v j • w j ∈ Lat i :=
  hw i (fun j => w.repr v j) ((w.sum_repr v).symm ▸ hv) j

include hw in
theorem matUnit_self_mem (j : Fin n) : matUnit F w j j ∈ P 0 := by
  intro i v hv
  rw [add_zero, matUnit_apply]
  exact repr_smul_mem 𝓛 hw hv j

include hϖ hnormal in
/-- Moving a scalar between two nonzero vectors shifts depths by the difference of indices. -/
theorem smul_mem_lattice_index_shift {v v' : V} (hv : v ≠ 0) (hv' : v' ≠ 0) (a : L) {k : ℤ}
    (h : a • v ∈ Lat k) :
    a • v' ∈ Lat (k - 𝓛.index hϖ v + 𝓛.index hϖ v') := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨d, hd⟩ := refinement_scalar_lattice_shift 𝓛 hnormal ha
  have hmem : v ∈ Lat (k - d) := (hd (k - d) v).mp (by rwa [sub_add_cancel])
  have hle : k - d ≤ 𝓛.index hϖ v := (𝓛.mem_iff_le_index hϖ hv _).mp hmem
  have hv'mem : v' ∈ Lat (k - d - 𝓛.index hϖ v + 𝓛.index hϖ v') :=
    (𝓛.mem_iff_le_index hϖ hv' _).mpr (by omega)
  have := (hd _ v').mpr hv'mem
  convert this using 2
  ring

include hϖ hnormal in
/-- The action of `a ∈ L` lies in `𝔓^k` exactly when `a v ∈ L_{ν(v)+k}`, for any `v ≠ 0`. -/
theorem subfieldEmbedding_mem_iff {v : V} (hv : v ≠ 0) (a : L) (k : ℤ) :
    subfieldEmbedding F L V a ∈ P k ↔ a • v ∈ Lat (𝓛.index hϖ v + k) := by
  constructor
  · intro h
    exact h _ v (𝓛.mem_lattice_index hϖ hv)
  · intro h i u hu
    rw [subfieldEmbedding_apply]
    by_cases hu0 : u = 0
    · rw [hu0, smul_zero]
      exact zero_mem _
    have h' := smul_mem_lattice_index_shift 𝓛 hϖ hnormal hv hu0 a h
    have hle : i ≤ 𝓛.index hϖ u := (𝓛.mem_iff_le_index hϖ hu0 i).mp hu
    exact 𝓛.antitone (by omega) h'

include hϖ hnormal hw in
/-- The sandwich `ε_{jl} z ε_{lj}` preserves every filtration step. -/
theorem matUnit_sandwich_mem {s : ℤ} {z : Module.End F V} (hz : z ∈ P s) (j l : Fin n) :
    matUnit F w j l * z * matUnit F w l j ∈ P s := by
  intro i v hv
  have hj : w j ≠ 0 := w.ne_zero j
  have hl : w l ≠ 0 := w.ne_zero l
  rw [Module.End.mul_apply, Module.End.mul_apply, matUnit_apply, matUnit_apply]
  have h1 := smul_mem_lattice_index_shift 𝓛 hϖ hnormal hj hl _ (repr_smul_mem 𝓛 hw hv j)
  have h2 := hz _ _ h1
  have h3 := repr_smul_mem 𝓛 hw h2 l
  have h4 := smul_mem_lattice_index_shift 𝓛 hϖ hnormal hl hj _ h3
  convert h4 using 2
  ring

include hϖ hnormal hw in
theorem diagonal_compress_mem {s : ℤ} {z : Module.End F V} (hz : z ∈ P s) (l : Fin n) :
    diagonal F w (compress F w l z) ∈ P s := by
  rw [diagonal_compress]
  exact Submodule.sum_mem _ fun j _ => matUnit_sandwich_mem 𝓛 hϖ hnormal hw hz j l

include hw in
/-- Every element of `𝔓^s` is the sum of its blocks `ε_{jj} z ε_{ll} ∈ 𝔓^s`. -/
theorem block_mem {s : ℤ} {z : Module.End F V} (hz : z ∈ P s) (j l : Fin n) :
    matUnit F w j j * z * matUnit F w l l ∈ P s := by
  have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration (matUnit_self_mem 𝓛 hw j) hz)
    (matUnit_self_mem 𝓛 hw l)
  simpa using h

theorem sum_blocks (z : Module.End F V) :
    ∑ j, ∑ l, matUnit F w j j * z * matUnit F w l l = z := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_matUnit_self, one_mul, mul_one]

end Filtration

end Langlands.BushnellKutzko
