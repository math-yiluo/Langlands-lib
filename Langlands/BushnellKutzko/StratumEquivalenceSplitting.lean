import Langlands.BushnellKutzko.RelativeFiltrationInversion

/-! # Relative splitting bases for a normalizing field

Helper results for `StratumEquivalenceStatement`. For a field `E` acting on `V` whose units
normalize an `𝔬_F`-lattice chain `𝓛`, there is an `E`-basis of `V` splitting every lattice
of the chain. The arguments are those of the private lemmas of
`Langlands.BushnellKutzko.RelativeFiltrationInversion`, restated here as public lemmas.
-/

open ValuativeRel
open scoped BigOperators

noncomputable section

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

/-- A nonzero scalar of a normalizing field shifts the chain by a fixed integer. -/
theorem exists_scalar_lattice_shift
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

/-- A representative of a coset of an `E`-subspace lying in every lattice that meets the
coset. -/
theorem exists_lattice_maximal_coset_rep (hϖ : Irreducible ϖ)
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

theorem coset_rep_smul_mem_of_add_mem
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

/-- A family `w` splits the chain if every summand of a linear combination lies in every
lattice containing the sum. -/
def RelativeSplits {n : ℕ} (w : Fin n → V) : Prop :=
  ∀ (i : ℤ) (c : Fin n → E), (∑ j, c j • w j) ∈ L i → ∀ j, c j • w j ∈ L i

theorem relativeSplits_finCons
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

/-- An `E`-basis of `V` splitting every lattice of a chain normalized by `E^×`. -/
theorem exists_relative_splitting_basis [FiniteDimensional F V] (hϖ : Irreducible ϖ)
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

end LocalField

omit [Algebra F E] [IsScalarTower F E V] in
/-- For a splitting basis, some scalar multiple of a basis vector has exact depth `i`. -/
theorem exists_scaled_basis_at_depth {n : ℕ} {w : Module.Basis (Fin n) E V}
    (hw : RelativeSplits (E := E) 𝓛 w) (i : ℤ) :
    ∃ (j : Fin n) (c : E), c • w j ∈ L i ∧ c • w j ∉ L (i + 1) := by
  obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt (𝓛.lattice_succ_lt i)
  have heq : (∑ j, w.coord j v • w j) = v := w.sum_repr v
  have hterm (j : Fin n) : w.coord j v • w j ∈ L i :=
    hw i (fun j => w.coord j v) (heq.symm ▸ hv) j
  by_contra! h
  apply hv'
  rw [← heq]
  exact Submodule.sum_mem _ fun j _ => h j _ (hterm j)

omit [Algebra F E] [IsScalarTower F E V] in
/-- For a splitting basis, each coordinate summand of a vector of `L_i` lies in `L_i`. -/
theorem coord_smul_mem {n : ℕ} {w : Module.Basis (Fin n) E V}
    (hw : RelativeSplits (E := E) 𝓛 w) {v : V} {i : ℤ} (hv : v ∈ L i) (k : Fin n) :
    w.coord k v • w k ∈ L i :=
  hw i (fun k => w.coord k v) ((w.sum_repr v).symm ▸ hv) k

end StratumEquivalence

end Langlands.BushnellKutzko
