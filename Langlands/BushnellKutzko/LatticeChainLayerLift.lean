import Langlands.BushnellKutzko.LatticeChainLayers

/-! # Lifting endomorphisms of successive lattice quotients -/

noncomputable section

open scoped Pointwise

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- Compatibility between a layer family and a unit which translates the chain. -/
def LayerFamilyCommutes (D : ∀ i : ℤ, Module.End O (𝓛.Layer i)) (g : 𝓛.stabilizer) : Prop :=
  ∀ (i j : ℤ) (h : j = i + 𝓛.stabilizerValuation g) (q : 𝓛.Layer i),
    𝓛.stabilizerLayerEquiv g i j h (D i q) = D j (𝓛.stabilizerLayerEquiv g i j h q)

section Flag

variable [IsLocalRing O]

/-- A compatible map on the quotients in a finite flag is obtained by splitting each
inclusion and its quotient over the residue field. -/
private theorem exists_interval_lift (D : ∀ i : ℤ, Module.End O (𝓛.Layer i)) (r : ℤ)
    (n : ℕ) (i : ℤ) (hin : r = i + n) (hper : r ≤ i + 𝓛.period) :
    ∃ f : Module.End O (𝓛.Interval i r), ∀ (j : ℤ) (hij : i ≤ j) (_ : j < r)
      (v : V) (hv : v ∈ 𝓛.lattice j), ∃ (w : V) (hw : w ∈ 𝓛.lattice j),
        f (𝓛.intervalMk i r v (𝓛.antitone hij hv)) =
          𝓛.intervalMk i r w (𝓛.antitone hij hw) ∧
        D j (𝓛.intervalMk j (j + 1) v hv) = 𝓛.intervalMk j (j + 1) w hw := by
  induction n generalizing i with
  | zero => exact ⟨0, fun j hij hjr => (by omega : False).elim⟩
  | succ n ih =>
    obtain ⟨f, hf⟩ := ih (i + 1) (by omega) (by omega)
    let := 𝓛.intervalResidueModule hper
    have := 𝓛.intervalResidueTower hper
    let := 𝓛.intervalResidueModule (i := i + 1) (j := r) (by omega)
    have := 𝓛.intervalResidueTower (i := i + 1) (j := r) (by omega)
    let k := IsLocalRing.ResidueField O
    let inc : 𝓛.Interval (i + 1) r →ₗ[k] 𝓛.Interval i r :=
      (𝓛.intervalMap (LinearMap.id : V →ₗ[O] V)
        (fun _ hv => 𝓛.antitone (by omega : i ≤ i + 1) hv)
        (fun _ hv => hv)).extendScalarsOfSurjective IsLocalRing.residue_surjective
    let proj : 𝓛.Interval i r →ₗ[k] 𝓛.Layer i :=
      (𝓛.intervalMap (LinearMap.id : V →ₗ[O] V) (fun _ hv => hv)
        (fun _ hv => 𝓛.antitone (by omega : i + 1 ≤ r) hv)).extendScalarsOfSurjective
          IsLocalRing.residue_surjective
    have hinc (v : V) (hv : v ∈ 𝓛.lattice (i + 1)) :
        inc (𝓛.intervalMk (i + 1) r v hv) =
          𝓛.intervalMk i r v (𝓛.antitone (by omega) hv) := rfl
    have hproj (v : V) (hv : v ∈ 𝓛.lattice i) :
        proj (𝓛.intervalMk i r v hv) = 𝓛.intervalMk i (i + 1) v hv := rfl
    have hinc_inj : Function.Injective inc := by
      intro q q' heq
      obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective (i + 1) r q
      obtain ⟨w, hw, rfl⟩ := 𝓛.intervalMk_surjective (i + 1) r q'
      simpa only [hinc, intervalMk_eq_iff] using heq
    have hproj_surj : Function.Surjective proj := by
      intro q
      obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
      exact ⟨𝓛.intervalMk i r v hv, hproj v hv⟩
    have hproj_inc (q : 𝓛.Interval (i + 1) r) : proj (inc q) = 0 := by
      obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective (i + 1) r q
      rwa [hinc, hproj, intervalMk_eq_zero_iff]
    obtain ⟨ret, hret⟩ := inc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinc_inj)
    obtain ⟨sec, hsec⟩ := proj.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hproj_surj)
    let fk : Module.End k (𝓛.Interval (i + 1) r) :=
      f.extendScalarsOfSurjective IsLocalRing.residue_surjective
    let Dk : Module.End k (𝓛.Layer i) := (D i).extendScalarsOfSurjective IsLocalRing.residue_surjective
    let g : Module.End k (𝓛.Interval i r) := inc.comp (fk.comp ret) + sec.comp (Dk.comp proj)
    have hret' (q : 𝓛.Interval (i + 1) r) : ret (inc q) = q := LinearMap.congr_fun hret q
    have hsec' (q : 𝓛.Layer i) : proj (sec q) = q := LinearMap.congr_fun hsec q
    have hg_inc (q : 𝓛.Interval (i + 1) r) : g (inc q) = inc (f q) := by
      change inc (fk (ret (inc q))) + sec (Dk (proj (inc q))) = inc (f q)
      rw [hret', hproj_inc, map_zero, map_zero, add_zero]
      rfl
    have hg_proj (q : 𝓛.Interval i r) : proj (g q) = D i (proj q) := by
      change proj (inc (fk (ret q)) + sec (Dk (proj q))) = D i (proj q)
      rw [map_add, hproj_inc, hsec', zero_add]
      rfl
    refine ⟨g.restrictScalars O, fun j hij hjr v hv => ?_⟩
    by_cases hji : j = i
    · subst j
      obtain ⟨w, hw, hwg⟩ := 𝓛.intervalMk_surjective i r (g (𝓛.intervalMk i r v hv))
      have hh := hg_proj (𝓛.intervalMk i r v hv)
      rw [← hwg, hproj, hproj] at hh
      exact ⟨w, hw, hwg.symm, hh.symm⟩
    · have hij' : i + 1 ≤ j := by omega
      obtain ⟨w, hw, hwf, hD⟩ := hf j hij' hjr v hv
      refine ⟨w, hw, ?_, hD⟩
      change g (𝓛.intervalMk i r v _) = 𝓛.intervalMk i r w _
      rw [← hinc v (𝓛.antitone hij' hv), hg_inc, hwf, hinc]

end Flag

section Global

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]

/-- A uniformizer acts by one period on the entire chain. -/
def uniformizerStabilizer {π : O} (hπ : Irreducible π) : 𝓛.stabilizer := by
  let πu := Units.mk0 (algebraMap O K π) ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hπ.ne_zero)
  refine ⟨Units.map (algebraMap K (Module.End K V)).toMonoidHom πu, fun i => ⟨i + 𝓛.period, ?_⟩⟩
  rw [𝓛.lattice_add_period, IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def]
  congr 1
  ext v
  exact algebraMap_smul K π v

@[simp] theorem uniformizerStabilizer_apply {π : O} (hπ : Irreducible π) (v : V) :
    ((𝓛.uniformizerStabilizer hπ).val : Module.End K V) v = (algebraMap O K π) • v := rfl

@[simp] theorem uniformizerStabilizer_shift {π : O} (hπ : Irreducible π) :
    𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ) = 𝓛.period := by
  symm
  apply 𝓛.stabilizerValuation_unique _ 0
  rw [𝓛.lattice_add_period, IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def]
  congr 1
  ext v
  exact algebraMap_smul K π v

/-- Periodically compatible endomorphisms of the layers lift to a chain-preserving endomorphism. -/
theorem exists_order_lift_layers {π : O} (hπ : Irreducible π)
    (D : ∀ i : ℤ, Module.End O (𝓛.Layer i))
    (hD : 𝓛.LayerFamilyCommutes D (𝓛.uniformizerStabilizer hπ)) :
    ∃ x : 𝓛.order, ∀ i : ℤ, 𝓛.layerAction x i = D i := by
  let r : ℤ := 𝓛.period
  have hr : 0 < r := by
    change (0 : ℤ) < (𝓛.period : ℤ)
    exact_mod_cast 𝓛.period_pos
  obtain ⟨f, hf⟩ := 𝓛.exists_interval_lift D r 𝓛.period 0 (by simp [r]) (by simp [r])
  have := 𝓛.isLattice 0
  have : Module.IsTorsionFree O K := Module.IsTorsionFree.trans_faithfulSMul O K K
  let q : 𝓛.lattice 0 →ₗ[O] 𝓛.Interval 0 r := (𝓛.intervalSubmodule 0 r).mkQ
  obtain ⟨u, hu⟩ := Module.projective_lifting_property q (f.comp q) (𝓛.intervalSubmodule 0 r).mkQ_surjective
  let b := Module.Free.chooseBasis O (𝓛.lattice 0)
  let x : Module.End K V := (b.extendOfIsLattice K).constr K (fun j => (u (b j) : V))
  have hx : (x.restrictScalars O).comp (𝓛.lattice 0).subtype = (𝓛.lattice 0).subtype.comp u := by
    apply b.ext
    intro j
    change x (b j : V) = (u (b j) : V)
    rw [← b.extendOfIsLattice_apply K j]
    exact Module.Basis.constr_basis _ _ _ j
  have hx' (v : V) (hv : v ∈ 𝓛.lattice 0) : x v = (u ⟨v, hv⟩ : V) :=
    LinearMap.congr_fun hx ⟨v, hv⟩
  let Good (i : ℤ) := ∀ (v : V) (hv : v ∈ 𝓛.lattice i),
    ∃ hxv : x v ∈ 𝓛.lattice i,
      D i (𝓛.intervalMk i (i + 1) v hv) = 𝓛.intervalMk i (i + 1) (x v) hxv
  have hinit (i : ℤ) (hi₀ : 0 ≤ i) (hir : i < r) : Good i := by
    intro v hv
    obtain ⟨w, hw, hfw, hwD⟩ := hf i hi₀ hir v hv
    let hv₀ := 𝓛.antitone hi₀ hv
    have hquot := LinearMap.congr_fun hu (⟨v, hv₀⟩ : 𝓛.lattice 0)
    change 𝓛.intervalMk 0 r (u ⟨v, hv₀⟩ : V) (u ⟨v, hv₀⟩).prop =
      f (𝓛.intervalMk 0 r v hv₀) at hquot
    have hdiff : x v - w ∈ 𝓛.lattice r :=
      (hx' v hv₀).symm ▸ (𝓛.intervalMk_eq_iff (u ⟨v, hv₀⟩).prop (𝓛.antitone hi₀ hw)).mp
        (hquot.trans hfw)
    have hxv : x v ∈ 𝓛.lattice i := sub_add_cancel (x v) w ▸
      add_mem (𝓛.antitone hir.le hdiff) hw
    refine ⟨hxv, hwD.trans ((𝓛.intervalMk_eq_iff hw hxv).mpr ?_)⟩
    rw [← neg_sub]
    exact neg_mem (𝓛.antitone (by omega) hdiff)
  have hstep (i : ℤ) : Good i ↔ Good (i + r) := by
    let g := 𝓛.uniformizerStabilizer hπ
    let a : Module.End K V := g.val
    have hshift : i + r = i + 𝓛.stabilizerValuation g := by simp [g, r]
    let t := 𝓛.stabilizerLayerEquiv g i (i + r) hshift
    have hmem (z : V) : a z ∈ 𝓛.lattice (i + r) ↔ z ∈ 𝓛.lattice i :=
      hshift.symm ▸ 𝓛.mem_lattice_stabilizer_iff g i z
    have hmk (v : V) (hv : v ∈ 𝓛.lattice i) :
        t (𝓛.intervalMk i (i + 1) v hv) =
          𝓛.intervalMk (i + r) (i + r + 1) (a v) ((hmem v).mpr hv) := rfl
    have hax (v : V) : a (x v) = x (a v) := by
      change (algebraMap O K π) • x v = x ((algebraMap O K π) • v)
      rw [map_smul]
    have hcompat (q : 𝓛.Layer i) : t (D i q) = D (i + r) (t q) := hD i (i + r) hshift q
    constructor
    · intro hi v hv
      let w := ((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) v
      have hav : a w = v := by
        change (g.val : Module.End K V) (((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) v) = v
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      have hw := (hmem w).mp (hav.symm ▸ hv)
      obtain ⟨hxw, heq⟩ := hi w hw
      have hxv : x v ∈ 𝓛.lattice (i + r) :=
        hav ▸ (hax w ▸ (hmem (x w)).mpr hxw)
      refine ⟨hxv, ?_⟩
      have heq' := congrArg t heq
      rw [hcompat, hmk, hmk] at heq'
      have hclass : 𝓛.intervalMk (i + r) (i + r + 1) (a w) ((hmem w).mpr hw) =
          𝓛.intervalMk (i + r) (i + r + 1) v hv :=
        (𝓛.intervalMk_eq_iff _ _).mpr (by rw [hav, sub_self]; exact zero_mem _)
      rw [hclass] at heq'
      exact heq'.trans ((𝓛.intervalMk_eq_iff _ _).mpr (by rw [hax, hav, sub_self]; exact zero_mem _))
    · intro hi v hv
      obtain ⟨hxav, heq⟩ := hi (a v) ((hmem v).mpr hv)
      have hxv := (hmem (x v)).mp (hax v ▸ hxav)
      refine ⟨hxv, t.injective ?_⟩
      rw [hcompat, hmk, hmk, heq]
      exact (𝓛.intervalMk_eq_iff _ _).mpr (by rw [hax, sub_self]; exact zero_mem _)
  have hall (i : ℤ) : Good i := by
    have h₀ := hinit (i % r) (Int.emod_nonneg _ hr.ne') (Int.emod_lt_of_pos _ hr)
    have hshift (n : ℤ) : Good (i % r + n * r) := by
      induction n using Int.induction_on with
      | zero => simpa using h₀
      | succ k ih =>
        convert (hstep (i % r + (k : ℤ) * r)).mp ih using 1
        ring
      | pred k ih =>
        apply (hstep (i % r + (-(k : ℤ) - 1) * r)).mpr
        convert ih using 1
        ring
    have h := hshift (i / r)
    rw [add_comm, Int.ediv_mul_add_emod] at h
    exact h
  have hxmem : x ∈ 𝓛.order := 𝓛.mem_order.mpr fun i v hv => (hall i v hv).choose
  refine ⟨⟨x, hxmem⟩, fun i => LinearMap.ext fun q' => ?_⟩
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q'
  exact (hall i v hv).choose_spec.symm

end Global

end Langlands.BushnellKutzko.LatticeChain
