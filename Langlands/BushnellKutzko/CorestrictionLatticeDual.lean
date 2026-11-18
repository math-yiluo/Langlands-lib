import Langlands.BushnellKutzko.UnitFiltration

/-! # Trace duality for a lattice chain over a DVR -/

noncomputable section

open Module
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} [CommRing O] [Field K]
  [Algebra O K] [IsDomain O] [IsFractionRing O K] [IsDiscreteValuationRing O]

/-- The maximal ideal of the DVR, viewed inside its fraction field. -/
def maximalIdealInField (O K : Type*) [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] :
    Set K :=
  algebraMap O K '' (IsLocalRing.maximalIdeal O : Set O)

omit [IsFractionRing O K] in
theorem mem_maximalIdealInField_iff {π : O} (hπ : Irreducible π) (x : K) :
    x ∈ maximalIdealInField O K ↔ ∃ a : O, algebraMap O K π * algebraMap O K a = x := by
  simp only [maximalIdealInField, hπ.maximalIdeal_eq, Set.mem_image, SetLike.mem_coe,
    Ideal.mem_span_singleton, dvd_def]
  constructor
  · rintro ⟨r, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (map_mul _ _ _).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨π * a, ⟨a, rfl⟩, map_mul _ _ _⟩

variable {V : Type uV} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem span_extended_basis {M : Submodule O V} [M.IsLattice K]
    {ι : Type*} (b : Basis ι O M) :
    Submodule.span O (Set.range (b.extendOfIsLattice K)) = M := by
  have hr : Set.range (b.extendOfIsLattice K) = M.subtype '' Set.range b := by
    ext x
    simp only [Set.mem_range, Set.mem_image, Basis.extendOfIsLattice_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

private theorem separates_lattice (M : Submodule O V) [M.IsLattice K] {v : V} (hv : v ∉ M) :
    ∃ f : V →ₗ[K] K, (∀ w ∈ M, f w ∈ maximalIdealInField O K) ∧
      f v ∉ maximalIdealInField O K := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let b := Module.Free.chooseBasis O M
  let c := b.extendOfIsLattice K
  have hcoords (w : V) : w ∈ M ↔ ∀ i, c.repr w i ∈ Set.range (algebraMap O K) := by
    have hmem : w ∈ Submodule.span O (Set.range c) ↔ w ∈ M :=
      Iff.of_eq (congrArg (fun N : Submodule O V => w ∈ N) (span_extended_basis b))
    exact hmem.symm.trans (Basis.mem_span_iff_repr_mem O c w)
  obtain ⟨i, hi⟩ : ∃ i, c.repr v i ∉ Set.range (algebraMap O K) := by
    simpa only [hcoords v, not_forall] using hv
  refine ⟨algebraMap O K π • c.coord i, ?_, ?_⟩
  · intro w hw
    obtain ⟨r, hr⟩ := (hcoords w).mp hw i
    refine (mem_maximalIdealInField_iff hπ _).mpr ⟨r, ?_⟩
    change algebraMap O K π * algebraMap O K r = algebraMap O K π * c.repr w i
    rw [hr]
  · intro h
    obtain ⟨r, hr⟩ := (mem_maximalIdealInField_iff hπ _).mp h
    have hπ0 : algebraMap O K π ≠ 0 := by
      rw [← map_zero (algebraMap O K)]
      exact (IsFractionRing.injective O K).ne hπ.ne_zero
    change algebraMap O K π * algebraMap O K r = algebraMap O K π * c.repr v i at hr
    apply hi
    exact ⟨r, mul_left_cancel₀ hπ0 hr⟩

/-- A finite submodule over a DVR is detected by linear forms tested against the maximal ideal. -/
theorem separates_fg_submodule (M : Submodule O V) (hM : M.FG) {v : V} (hv : v ∉ M) :
    ∃ f : V →ₗ[K] K, (∀ w ∈ M, f w ∈ maximalIdealInField O K) ∧
      f v ∉ maximalIdealInField O K := by
  let W := Submodule.span K (M : Set V)
  let i : W →ₗ[O] V := W.subtype.restrictScalars O
  let N := M.comap i
  have hmap : N.map i = M := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hw
      exact ⟨⟨w, Submodule.subset_span hw⟩, hw, rfl⟩
  by_cases h : v ∈ W
  · have : N.IsLattice K := by
      refine ⟨Submodule.fg_of_fg_map_injective i Subtype.val_injective (hmap ▸ hM), ?_⟩
      apply (Submodule.map_injective_of_injective W.injective_subtype)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
      rw [show W.subtype '' (N : Set W) = (M : Set V) from
        congrArg (fun T : Submodule O V => (T : Set V)) hmap]
    obtain ⟨f, hf, hvf⟩ := separates_lattice N (v := ⟨v, h⟩) hv
    obtain ⟨g, hg⟩ := f.exists_extend
    refine ⟨g, fun w hw => ?_, ?_⟩
    · have hw' : w ∈ W := Submodule.subset_span hw
      have he := LinearMap.congr_fun hg ⟨w, hw'⟩
      exact he ▸ hf ⟨w, hw'⟩ hw
    · have he := LinearMap.congr_fun hg ⟨v, h⟩
      exact he ▸ hvf
  · obtain ⟨g, hg, hgv⟩ := LinearMap.exists_extend_of_notMem (0 : W →ₗ[K] K) h 1
    refine ⟨g, fun w hw => ?_, ?_⟩
    · have he : g w = 0 := LinearMap.congr_fun hg ⟨w, Submodule.subset_span hw⟩
      rw [he]
      exact ⟨0, zero_mem _, map_zero _⟩
    · rw [hgv]
      rintro ⟨a, ha, ha1⟩
      have : a = 1 := (IsFractionRing.injective O K) (by simpa using ha1)
      exact Ideal.one_notMem (IsLocalRing.maximalIdeal O) (this ▸ ha)

namespace LatticeChain

variable (𝓛 : LatticeChain O K V)

omit [IsFractionRing O K] in
theorem lattice_add_period_uniformizer {π : O} (hπ : Irreducible π) (i : ℤ) :
    𝓛.lattice (i + 𝓛.period) = (algebraMap O K π) • 𝓛.lattice i := by
  rw [𝓛.lattice_add_period, IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul]
  ext v
  simp only [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]

/-- Each endomorphism filtration step is a finite module of endomorphisms. -/
theorem fg_endFiltration (n : ℤ) : (𝓛.endFiltration n).FG := by
  have := 𝓛.isLattice 0
  have := 𝓛.isLattice n
  let b := Module.Free.chooseBasis O (𝓛.lattice 0)
  let f : 𝓛.endFiltration n →ₗ[O] (Module.Free.ChooseBasisIndex O (𝓛.lattice 0) → 𝓛.lattice n) :=
    { toFun := fun x j => ⟨x.val (b j), by simpa using x.property 0 (b j) (b j).property⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (b.extendOfIsLattice K).ext
    intro j
    rw [Basis.extendOfIsLattice_apply]
    exact congrArg (fun v : 𝓛.lattice n => (v : V)) (congrFun h j)
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.of_injective f hf

private theorem rankOne_mem_endFiltration {n i : ℤ} (v : V) (hv : v ∈ 𝓛.lattice i)
    (f : V →ₗ[K] K) (hf : ∀ w ∈ 𝓛.lattice (i + 1 - n), f w ∈ maximalIdealInField O K) :
    f.smulRight v ∈ 𝓛.endFiltration n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let p : ℤ := 𝓛.period
  let a := algebraMap O K π
  have ha : a ≠ 0 := by
    change algebraMap O K π ≠ 0
    rw [← map_zero (algebraMap O K)]
    exact (IsFractionRing.injective O K).ne hπ.ne_zero
  have hp : 0 < p := Int.natCast_pos.mpr 𝓛.period_pos
  have hshift j : 𝓛.lattice (j + p) = a • 𝓛.lattice j := 𝓛.lattice_add_period_uniformizer hπ j
  let P (j : ℤ) := ∀ w ∈ 𝓛.lattice j, f w • v ∈ 𝓛.lattice (j + n)
  have hper : Function.Periodic P p := by
    intro j
    apply propext
    change (∀ w ∈ 𝓛.lattice (j + p), f w • v ∈ 𝓛.lattice (j + p + n)) ↔ _
    rw [show j + p + n = j + n + p by omega, hshift, hshift]
    constructor
    · intro h w hw
      obtain ⟨z, hz, hza⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
        (h (a • w) (Submodule.smul_mem_pointwise_smul _ _ _ hw))
      rw [map_smul, smul_assoc] at hza
      exact smul_right_injective V ha hza ▸ hz
    · intro h w hw
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
      rw [map_smul, smul_assoc]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (h z hz)
  intro j
  change P j
  let k := i + 1 - n - p
  let r := (j - k) % p
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hp.ne'
  have hrp : r < p := Int.emod_lt_of_pos _ hp
  have hj : j - ((j - k) / p) * p = k + r := by
    dsimp [r]
    have := Int.emod_add_ediv_mul (j - k) p
    omega
  rw [← hper.sub_int_mul_eq ((j - k) / p)]
  change P (j - ((j - k) / p) * p)
  rw [hj]
  intro w hw
  have hwk : w ∈ 𝓛.lattice k := 𝓛.antitone (by omega) hw
  have hwa : a • w ∈ 𝓛.lattice (i + 1 - n) := by
    rw [show i + 1 - n = k + p by dsimp [k]; omega, hshift]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hwk
  obtain ⟨c, hc⟩ := (mem_maximalIdealInField_iff hπ _).mp (hf _ hwa)
  have hfw : f w = algebraMap O K c := by
    apply mul_left_cancel₀ ha
    rw [map_smul] at hc
    exact hc.symm
  rw [hfw, algebraMap_smul]
  exact 𝓛.antitone (by dsimp [k]; omega) (Submodule.smul_mem _ _ hv)

omit [IsDomain O] [IsFractionRing O K] [IsDiscreteValuationRing O] in
private theorem pow_mem_endFiltration_one {x : Module.End K V} (hx : x ∈ 𝓛.endFiltration 1)
    (k : ℕ) : x ^ k ∈ 𝓛.endFiltration k := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact 𝓛.order.one_mem
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    exact 𝓛.mul_mem_endFiltration ih hx

/-- The trace of an endomorphism lowering the lattice chain lies in the maximal ideal. -/
theorem trace_mem_maximalIdealInField {x : Module.End K V} (hx : x ∈ 𝓛.endFiltration 1) :
    LinearMap.trace K V x ∈ maximalIdealInField O K := by
  classical
  let M := 𝓛.lattice 0
  have : M.IsLattice K := 𝓛.isLattice 0
  let b := Module.Free.chooseBasis O M
  let c := b.extendOfIsLattice K
  have hxM : ∀ v ∈ M, x v ∈ M := by
    intro v hv
    exact 𝓛.antitone (by decide : (0 : ℤ) ≤ 0 + 1) (hx 0 v hv)
  let f : Module.End O M := (x.restrictScalars O).restrict hxM
  let A := LinearMap.toMatrix b b f
  let m := IsLocalRing.maximalIdeal O
  let q := Ideal.Quotient.mk m
  have hcoord (i : Module.Free.ChooseBasisIndex O M) :
      ((c.coord i).restrictScalars O).comp M.subtype =
        (Algebra.linearMap O K).comp (b.coord i) := by
    apply b.ext
    intro j
    change c.coord i (b j : V) = algebraMap O K (b.coord i (b j))
    have hj : c j = (b j : V) := Basis.extendOfIsLattice_apply K b j
    rw [← hj]
    by_cases hij : j = i <;>
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, hij, ite_true, ite_false,
        map_one, map_zero]
  have hA : A.map (algebraMap O K) = LinearMap.toMatrix c c x := by
    ext i j
    simp only [A, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hj : c j = (b j : V) := Basis.extendOfIsLattice_apply K b j
    rw [hj]
    exact (LinearMap.congr_fun (hcoord i) (f (b j))).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ m := by
    change π ∈ IsLocalRing.maximalIdeal O
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hfv (k : ℕ) (w : M) : ((f ^ k) w : V) = (x ^ k) (w : V) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change x ((f ^ k) w : V) = x ((x ^ k) (w : V))
      rw [ih]
  have hnil : IsNilpotent (A.map q) := by
    refine ⟨𝓛.period, ?_⟩
    rw [← Matrix.map_pow]
    change (LinearMap.toMatrixAlgEquiv b f ^ 𝓛.period).map q = 0
    rw [← map_pow]
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply, Matrix.zero_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hshift := 𝓛.pow_mem_endFiltration_one hx 𝓛.period 0 (b j) (b j).property
    rw [𝓛.lattice_add_period_uniformizer hπ] at hshift
    obtain ⟨v, hv, heq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hshift
    have heq' : (f ^ 𝓛.period) (b j) = π • (⟨v, hv⟩ : M) := by
      apply Subtype.ext
      change _ = π • v
      rw [hfv, ← algebraMap_smul K, heq]
    rw [heq', map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact m.mul_mem_right _ hπm
  have ht : Matrix.trace A ∈ m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [AddMonoidHom.map_trace]
    exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  exact ⟨Matrix.trace A, ht, by
    rw [AddMonoidHom.map_trace, hA, LinearMap.trace_eq_matrix_trace K c]⟩

/-- The maximal-ideal trace pairing exchanges filtration indices `n` and `1 - n`. -/
theorem mem_endFiltration_iff_trace_mul [FiniteDimensional K V] (n : ℤ) (x : Module.End K V) :
    x ∈ 𝓛.endFiltration (1 - n) ↔
      ∀ y ∈ 𝓛.endFiltration n, LinearMap.trace K V (x * y) ∈ maximalIdealInField O K := by
  constructor
  · intro hx y hy
    apply 𝓛.trace_mem_maximalIdealInField
    simpa using 𝓛.mul_mem_endFiltration hx hy
  · intro h
    by_contra hx
    have hbad : ∃ i v, v ∈ 𝓛.lattice i ∧ x v ∉ 𝓛.lattice (i + (1 - n)) := by
      by_contra! hgood
      exact hx hgood
    obtain ⟨i, v, hv, hxv⟩ := hbad
    obtain ⟨f, hf, hfx⟩ :=
      separates_fg_submodule (K := K) _ (𝓛.isLattice _).fg hxv
    have hy := 𝓛.rankOne_mem_endFiltration v hv f (by simpa only [add_sub_assoc] using hf)
    have heq : x * f.smulRight v = f.smulRight (x v) := by
      ext w
      simp [Module.End.mul_apply]
    have htrace := h _ hy
    rw [heq, LinearMap.trace_smulRight] at htrace
    exact hfx htrace

end LatticeChain

end Langlands.BushnellKutzko
