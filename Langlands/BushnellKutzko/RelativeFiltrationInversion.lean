import Langlands.BushnellKutzko.AdjointCentralizer

/-! # Inverse steps of the relative filtration -/

open ValuativeRel
open scoped BigOperators

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

private theorem exists_scalar_lattice_shift
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer) {c : E} (hc : c ≠ 0) :
    ∃ d : ℤ, ∀ (i : ℤ) (v : V), c • v ∈ L (i + d) ↔ v ∈ L i := by
  let u := Units.mk0 c hc
  let g : 𝓛.stabilizer := ⟨subfieldUnits F E V u, hnormal u⟩
  refine ⟨𝓛.stabilizerValuation g, fun i v => ?_⟩
  rw [← 𝓛.map_lattice_stabilizer g i, Submodule.mem_map]
  change (∃ w ∈ L i, c • w = c • v) ↔ v ∈ L i
  exact ⟨fun ⟨w, hw, heq⟩ => (smul_right_injective V hc heq) ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]}

private theorem exists_lattice_maximal_coset_rep (hϖ : Irreducible ϖ)
    (U : Submodule E V) {x : V} (hx : x ∉ U) :
    ∃ w : V, w - x ∈ U ∧ ∀ i : ℤ, (∃ y ∈ L i, y - x ∈ U) → w ∈ L i := by
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
  have hsep : ∃ i : ℤ, f x ∉ L i := by
    by_contra! h
    exact hx ((hker x).mp (𝓛.lattice_eq_zero_of_forall h))
  obtain ⟨i, hi⟩ := hsep
  let C : Set ℤ := {j | ∃ y ∈ L j, y - x ∈ U}
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

private theorem coset_rep_smul_mem_of_add_mem
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
    (U : Submodule E V) {w : V} (hw : ∀ j : ℤ, (∃ y ∈ L j, y - w ∈ U) → w ∈ L j)
    {u : V} (hu : u ∈ U) (c : E) (i : ℤ) (h : u + c • w ∈ L i) : c • w ∈ L i := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨d, hd⟩ := exists_scalar_lattice_shift 𝓛 hnormal hc
  let y := c⁻¹ • u + w
  have hy : c • y = u + c • w := by rw [smul_add, smul_inv_smul₀ hc]
  have hyL : y ∈ L (i - d) := (hd (i - d) y).mp (by rwa [hy, sub_add_cancel])
  have hyU : y - w ∈ U := by
    change c⁻¹ • u + w - w ∈ U
    rw [add_sub_cancel_right]
    exact U.smul_mem _ hu
  have hcw := (hd (i - d) w).mpr (hw _ ⟨y, hyL, hyU⟩)
  rwa [sub_add_cancel] at hcw

private def RelativeSplits {n : ℕ} (w : Fin n → V) : Prop :=
  ∀ (i : ℤ) (c : Fin n → E), (∑ j, c j • w j) ∈ L i → ∀ j, c j • w j ∈ L i

private theorem relativeSplits_finCons
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
    {n : ℕ} {w : Fin n → V} (hw : RelativeSplits (E := E) 𝓛 w) {v : V}
    (hv : ∀ j : ℤ, (∃ y ∈ L j, y - v ∈ Submodule.span E (Set.range w)) → v ∈ L j) :
    RelativeSplits (E := E) 𝓛 (Fin.cons v w) := by
  intro i c h j
  let u := ∑ r : Fin n, c r.succ • w r
  have hu : u ∈ Submodule.span E (Set.range w) := Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self r))
  have hsum : u + c 0 • v ∈ L i := by
    rw [Fin.sum_univ_succ] at h
    simpa only [u, Fin.cons_zero, Fin.cons_succ, add_comm] using h
  have hl := coset_rep_smul_mem_of_add_mem 𝓛 hnormal _ hv hu (c 0) i hsum
  have huL : u ∈ L i := by
    have hs := (L i).sub_mem hsum hl
    rwa [add_sub_cancel_right] at hs
  refine Fin.cases ?_ (fun r => ?_) j
  · simpa only [Fin.cons_zero] using hl
  · simpa only [Fin.cons_succ] using hw i (fun r => c r.succ) huL r

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]}

private theorem exists_relative_splitting_basis [FiniteDimensional F V] (hϖ : Irreducible ϖ)
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) E V), RelativeSplits (E := E) 𝓛 w := by
  let : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let S : Set ℕ := {n | ∃ w : Fin n → V, LinearIndependent E w ∧ RelativeSplits (E := E) 𝓛 w}
  have hne : S.Nonempty := by
    refine ⟨0, Fin.elim0, linearIndependent_empty_type, fun _ _ _ j => Fin.elim0 j⟩
  have hbound (n : ℕ) (hn : n ∈ S) : n ≤ Module.finrank E V := by
    obtain ⟨w, hw, _⟩ := hn
    simpa only [Fintype.card_fin] using hw.fintype_card_le_finrank
  have hfin : S.Finite := (Set.finite_le_nat (Module.finrank E V)).subset fun n hn => hbound n hn
  have hmax := hne.isGreatest_csSup hfin
  obtain ⟨w, hw, hsplit⟩ := hmax.1
  let U := Submodule.span E (Set.range w)
  have hU : U = ⊤ := by
    by_contra hne
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    obtain ⟨v, hvU, hv⟩ := exists_lattice_maximal_coset_rep 𝓛 hϖ U hx
    have hv' : v ∉ U := fun hv => hx (sub_sub_cancel v x ▸ U.sub_mem hv hvU)
    have hvmax (i : ℤ) (hi : ∃ y ∈ L i, y - v ∈ U) : v ∈ L i := by
      obtain ⟨y, hy, hyv⟩ := hi
      exact hv i ⟨y, hy, sub_add_sub_cancel y v x ▸ U.add_mem hyv hvU⟩
    have hs : sSup S + 1 ∈ S := ⟨Fin.cons v w, hw.finCons hv',
      relativeSplits_finCons 𝓛 hnormal hsplit hvmax⟩
    exact (Nat.not_succ_le_self _) (hmax.2 hs)
  let basis := Module.Basis.mk hw hU.ge
  refine ⟨sSup S, basis, ?_⟩
  simpa only [basis, Module.Basis.coe_mk] using hsplit

omit [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V] in
private theorem exists_exact_lattice_depth (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) :
    ∃ i : ℤ, v ∈ L i ∧ v ∉ L (i + 1) := by
  let C : Set ℤ := {i | v ∈ L i}
  have hne : C.Nonempty := 𝓛.exists_lattice_depth hϖ v
  have hsep : ∃ i, v ∉ L i := by
    by_contra! h
    exact hv (𝓛.lattice_eq_zero_of_forall h)
  obtain ⟨i, hi⟩ := hsep
  have hbdd : BddAbove C := ⟨i, fun j hj =>
    le_of_not_ge fun hij => hi (𝓛.antitone hij hj)⟩
  refine ⟨sSup C, Int.csSup_mem hne hbdd, fun h => ?_⟩
  have hle := le_csSup hbdd (show sSup C + 1 ∈ C from h)
  omega

end LocalField

omit [Algebra F E] [IsScalarTower F E V] in
private theorem exists_scaled_basis_at_depth {n : ℕ} {w : Module.Basis (Fin n) E V}
    (hw : RelativeSplits (E := E) 𝓛 w) (i : ℤ) :
    ∃ (j : Fin n) (c : E), c • w j ∈ L i ∧ c • w j ∉ L (i + 1) := by
  obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt (𝓛.lattice_succ_lt i)
  have heq : (∑ j, w.coord j v • w j) = v := w.sum_repr v
  have hterm (j : Fin n) : w.coord j v • w j ∈ L i := hw i (fun j => w.coord j v) (heq.symm ▸ hv) j
  by_contra! h
  apply hv'
  rw [← heq]
  exact Submodule.sum_mem _ fun j _ => h j _ (hterm j)

private theorem smul_mem_lattice_of_depth
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
    {v w : V} {i m : ℤ} (hv' : v ∉ L (i + 1)) (hw : w ∈ L (i + m))
    (c : E) {j : ℤ} (hcv : c • v ∈ L j) : c • w ∈ L (j + m) := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨d, hd⟩ := exists_scalar_lattice_shift 𝓛 hnormal hc
  have hmem : v ∈ L (j - d) := (hd (j - d) v).mp (by rwa [sub_add_cancel])
  have hle : j - d ≤ i := by
    by_contra! h
    exact hv' (𝓛.antitone (show i + 1 ≤ j - d by omega) hmem)
  have hw' := (hd (j - d + m) w).mpr (𝓛.antitone (show j - d + m ≤ i + m by omega) hw)
  rwa [add_right_comm (j - d) m d, sub_add_cancel] at hw'

/-- The relative steps of opposite depths multiply to a submodule containing the identity. -/
theorem one_mem_centralizerLattice_mul_neg [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F V] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (β : E)
    (hnormal : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer) (m : ℤ) :
    (1 : A) ∈ centralizerLattice 𝓛 (subfieldEmbedding F E V β) m *
      centralizerLattice 𝓛 (subfieldEmbedding F E V β) (-m) := by
  let b := subfieldEmbedding F E V β
  let Q := centralizerLattice 𝓛 b
  obtain ⟨n, w, hw⟩ := exists_relative_splitting_basis 𝓛 hϖ hnormal
  have hdepth (i : Fin n) := exists_exact_lattice_depth 𝓛 hϖ (w.ne_zero i)
  choose depth hw₁ hw₂ using hdepth
  let diagonal (i : Fin n) : A := ((w.coord i).smulRight (w i)).restrictScalars F
  have hsum : ∑ i, diagonal i = (1 : A) := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.sum_apply]
    exact w.sum_repr v
  have hmem {p : ℤ} {z : Module.End E V}
      (hz : ∀ j, ∀ v ∈ L j, z v ∈ L (j + p)) : z.restrictScalars F ∈ Q p := by
    refine (mem_centralizerLattice_iff 𝓛).mpr ⟨𝓛.mem_endFiltration.mpr hz, ?_⟩
    apply LinearMap.ext
    intro v
    change β • z v - z (β • v) = 0
    rw [z.map_smul, sub_self]
  have hcoord {v : V} {j : ℤ} (hv : v ∈ L j) (i : Fin n) : w.coord i v • w i ∈ L j :=
    hw j (fun i => w.coord i v) ((w.sum_repr v).symm ▸ hv) i
  rw [← hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨j, c, hc₁, hc₂⟩ := exists_scaled_basis_at_depth 𝓛 hw (depth i - m)
  have hc : c ≠ 0 := by
    intro h
    exact hc₂ (by simp [h])
  let x := (w.coord j).smulRight (c⁻¹ • w i)
  let y := (w.coord i).smulRight (c • w j)
  have hx : x.restrictScalars F ∈ Q m := hmem fun p v hv => by
    have hvc : (w.coord j v * c⁻¹) • (c • w j) ∈ L p := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
      exact hcoord hv j
    have hwi : w i ∈ L (depth i - m + m) := by simpa only [sub_add_cancel] using hw₁ i
    have hs := smul_mem_lattice_of_depth 𝓛 hnormal hc₂ hwi _ hvc
    change w.coord j v • (c⁻¹ • w i) ∈ L (p + m)
    rwa [smul_smul]
  have hy : y.restrictScalars F ∈ Q (-m) := hmem fun p v hv =>
    smul_mem_lattice_of_depth 𝓛 hnormal (hw₂ i) (by simpa only [sub_eq_add_neg] using hc₁)
      (w.coord i v) (hcoord hv i)
  have hxy : x.restrictScalars F * y.restrictScalars F = diagonal i := by
    apply LinearMap.ext
    intro v
    change w.coord j (w.coord i v • (c • w j)) • (c⁻¹ • w i) = w.coord i v • w i
    simp [smul_smul, hc]
  exact hxy ▸ Submodule.mul_mem_mul hx hy

end Langlands.BushnellKutzko
