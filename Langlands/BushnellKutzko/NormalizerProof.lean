import Langlands.BushnellKutzko.NormalizerStatement

/-! # The normalizer of a lattice chain -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

section LocalField

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private def conjugate (g : G) : A ≃+* A :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv g).conjRingEquiv

private theorem conjugate_apply (g : G) (x : A) :
    conjugate g x = (g : A) * x * (↑g⁻¹ : A) := rfl

private theorem conjugate_image_eq {g : G} {S : Set A}
    (hg : Set.MapsTo (conjugate g) S S) (hgi : Set.MapsTo (conjugate g⁻¹) S S) :
    conjugate g '' S = S := by
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr hg) ?_
  intro x hx
  refine ⟨conjugate g⁻¹ x, hgi hx, ?_⟩
  simp only [conjugate_apply, inv_inv, ← mul_assoc, Units.mul_inv, one_mul]
  exact Units.mul_inv_cancel_right x g

private theorem image_eval_conjugate {g : G} {S : Set A}
    (h : conjugate g '' S = S) (z : V) :
    (g : A) '' ((fun x : A => x z) '' S) =
      (fun x : A => x ((g : A) z)) '' S := by
  calc
    _ = (fun x : A => x ((g : A) z)) '' (conjugate g '' S) := by
      rw [Set.image_image, Set.image_image]
      apply congrArg (fun f : A → V => f '' S)
      funext x
      simp only [conjugate_apply, ← Module.End.mul_apply, mul_assoc, Units.inv_mul, mul_one]
    _ = _ := by rw [h]

variable [ValuativeRel F]

local notation "O" => 𝒪[F]

private theorem integer_smul_injective {c : O} (hc : c ≠ 0) :
    Function.Injective (fun z : V => c • z) := by
  intro x y h
  change c • x = c • y at h
  rw [← algebraMap_smul F c x, ← algebraMap_smul F c y] at h
  exact smul_right_injective V (fun h' => hc (Subtype.ext h')) h

private theorem exists_layer_vector (𝓛 : LatticeChain O F V) (i : ℤ) :
    ∃ z : V, z ∈ 𝓛.lattice i ∧ z ∉ 𝓛.lattice (i + 1) :=
  SetLike.exists_of_lt (𝓛.lattice_succ_lt i)

private theorem unit_apply_ne_zero_of_layer (𝓛 : LatticeChain O F V)
    (g : G) {i : ℤ} {z : V} (hz : z ∉ 𝓛.lattice (i + 1)) : (g : A) z ≠ 0 := by
  intro h
  apply hz
  have h' := congrArg (fun v => (↑g⁻¹ : A) v) h
  have he : z = 0 := by simpa [← Module.End.mul_apply] using h'
  rw [he]
  exact zero_mem _

section LatticeRecovery

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem lattice_add_period_mul (𝓛 : LatticeChain O F V) (i : ℤ) (k : ℕ) :
    𝓛.lattice (i + (k : ℤ) * 𝓛.period) = 𝓂[F] ^ k • 𝓛.lattice i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show i + ((k + 1 : ℕ) : ℤ) * 𝓛.period = (i + (k : ℤ) * 𝓛.period) + 𝓛.period by
      push_cast; ring, 𝓛.lattice_add_period, ih, jacobson_integer_eq_maximalIdeal,
      pow_succ', mul_smul]

private theorem lattice_add_period_smul (𝓛 : LatticeChain O F V)
    {π : O} (hπ : Irreducible π) (i : ℤ) :
    𝓛.lattice (i + 𝓛.period) = π • 𝓛.lattice i := by
  rw [𝓛.lattice_add_period, jacobson_integer_eq_maximalIdeal,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Submodule.ideal_span_singleton_smul]

/-- A nonzero vector is in a successive difference of the chain. -/
private theorem exists_layer (𝓛 : LatticeChain O F V) {z : V} (hz : z ≠ 0) :
    ∃ i : ℤ, z ∈ 𝓛.lattice i ∧ z ∉ 𝓛.lattice (i + 1) := by
  let S : Set ℤ := {i | z ∈ 𝓛.lattice i}
  have hne : S.Nonempty := by
    have hspan : z ∈ Submodule.span F (𝓛.lattice 0 : Set V) := by
      rw [(𝓛.isLattice 0).span_eq_top]
      exact Submodule.mem_top
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors O) F (𝓛.lattice 0 : Set V) z hspan
    change (d : O) • z ∈ Submodule.span O (𝓛.lattice 0 : Set V) at hd
    rw [Submodule.span_eq] at hd
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero d.2) hπ
    rw [ha, mul_smul] at hd
    have hpow : π ^ k • z ∈ 𝓛.lattice 0 := by
      simpa [← mul_smul, ← Units.val_mul] using (𝓛.lattice 0).smul_mem (↑a⁻¹ : O) hd
    have hshift := lattice_add_period_mul 𝓛 (-((k : ℤ) * 𝓛.period)) k
    rw [neg_add_cancel, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hshift
    rw [hshift] at hpow
    obtain ⟨y, hy, hyz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hpow
    exact ⟨_, integer_smul_injective (pow_ne_zero k hπ.ne_zero) hyz ▸ hy⟩
  have hb : BddAbove S := by
    by_contra hunbounded
    have hall (i : ℤ) : z ∈ 𝓛.lattice i := by
      obtain ⟨j, hj, hij⟩ := not_bddAbove_iff.mp hunbounded i
      exact 𝓛.antitone hij.le hj
    let z₀ : 𝓛.lattice 0 := ⟨z, hall 0⟩
    let : (𝓛.lattice 0).IsLattice F := 𝓛.isLattice 0
    have hmem : z₀ ∈ ⨅ k : ℕ, 𝓂[F] ^ k • (⊤ : Submodule O (𝓛.lattice 0)) := by
      rw [Submodule.mem_iInf]
      intro k
      apply (Submodule.mem_smul_top_iff (𝓂[F] ^ k) (𝓛.lattice 0) z₀).2
      rw [← lattice_add_period_mul 𝓛 0 k]
      exact hall _
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top,
      Submodule.mem_bot] at hmem
    exact hz (congrArg Subtype.val hmem)
  refine ⟨sSup S, Int.csSup_mem hne hb, ?_⟩
  intro h
  have hle := le_csSup hb (show sSup S + 1 ∈ S from h)
  omega

/-- A vector primitive in a lattice has an integral linear functional taking a unit value. -/
private theorem exists_integral_functional {M : Submodule O V} [M.IsLattice F] {z : V}
    (hz : z ∈ M) (hz' : z ∉ 𝓂[F] • M) :
    ∃ (f : V →ₗ[F] F) (a : Oˣ), f z = (↑(a : O) : F) ∧
      ∀ y ∈ M, ∃ c : O, f y = (c : F) := by
  let b := Module.Free.chooseBasis O M
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex O M)
  let z₀ : M := ⟨z, hz⟩
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (b.repr z₀ j) := by
    by_contra! h
    apply hz'
    apply (Submodule.mem_smul_top_iff 𝓂[F] M z₀).1
    rw [← b.sum_repr z₀]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    simpa [IsLocalRing.mem_maximalIdeal] using h j
  let f := (b.extendOfIsLattice F).coord j
  have hcoord : (f.restrictScalars O).comp M.subtype = (Algebra.linearMap O F).comp (b.coord j) := by
    apply b.ext
    intro k
    change f (b k : V) = algebraMap O F (b.coord j (b k))
    simp only [f, ← b.extendOfIsLattice_apply F k, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    split <;> simp
  have hcoord_apply (y : M) : f (y : V) = (↑(b.repr y j) : F) :=
    LinearMap.congr_fun hcoord y
  exact ⟨f, hj.unit, by simpa only [hj.unit_spec] using hcoord_apply z₀,
    fun y hy => ⟨b.repr ⟨y, hy⟩ j, hcoord_apply ⟨y, hy⟩⟩⟩

/-- An integral functional on `L_{i+1-e}` times a vector of `L_{i+n}` lies in `P^n`. -/
private theorem rank_one_mem_filtration (𝓛 : LatticeChain O F V)
    {i n : ℤ} {f : V →ₗ[F] F} {z : V}
    (hf : ∀ y ∈ 𝓛.lattice (i + 1 - 𝓛.period), ∃ c : O, f y = (c : F))
    (hz : z ∈ 𝓛.lattice (i + n)) : f.smulRight z ∈ 𝓛.endFiltration n := by
  let x := f.smulRight z
  let P : ℤ → Prop := fun j => ∀ y ∈ 𝓛.lattice j, x y ∈ 𝓛.lattice (j + n)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hper : Function.Periodic P (𝓛.period : ℤ) := by
    intro j
    apply propext
    change (∀ y ∈ 𝓛.lattice (j + 𝓛.period), x y ∈ 𝓛.lattice (j + 𝓛.period + n)) ↔
      (∀ y ∈ 𝓛.lattice j, x y ∈ 𝓛.lattice (j + n))
    rw [add_right_comm j, lattice_add_period_smul 𝓛 hπ, lattice_add_period_smul 𝓛 hπ]
    constructor
    · intro h y hy
      have hym := h (π • y) (Submodule.smul_mem_pointwise_smul _ _ _ hy)
      rw [← LinearMap.restrictScalars_apply O, map_smul] at hym
      obtain ⟨t, ht, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hym
      exact integer_smul_injective hπ.ne_zero he ▸ ht
    · intro h y hy
      obtain ⟨t, ht, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [← LinearMap.restrictScalars_apply O, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (h t ht)
  apply (𝓛.mem_endFiltration).2
  intro j
  let j₀ := i + 1 - (𝓛.period : ℤ)
  let k := (j - j₀) % (𝓛.period : ℤ)
  have hp : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hk₀ := Int.emod_nonneg (j - j₀) hp.ne'
  have hk₁ := Int.emod_lt_of_pos (j - j₀) hp
  have hj : j₀ + k = j - ((j - j₀) / (𝓛.period : ℤ)) * (𝓛.period : ℤ) := by
    dsimp [k]
    rw [Int.emod_def]
    ring
  have hperiodic : P (j - ((j - j₀) / (𝓛.period : ℤ)) * (𝓛.period : ℤ)) = P j :=
    hper.sub_int_mul_eq (x := j) _
  change P j
  rw [← hperiodic, ← hj]
  intro y hy
  obtain ⟨c, hc⟩ := hf y (𝓛.antitone (show j₀ ≤ j₀ + k by omega) hy)
  have hle : j₀ + k + n ≤ i + n := by omega
  change f y • z ∈ 𝓛.lattice (j₀ + k + n)
  change f y = algebraMap O F c at hc
  rw [hc, algebraMap_smul]
  exact (𝓛.lattice _).smul_mem c (𝓛.antitone hle hz)

private theorem exists_layer_functional (𝓛 : LatticeChain O F V)
    {i : ℤ} {z : V} (hz : z ∈ 𝓛.lattice i) (hz' : z ∉ 𝓛.lattice (i + 1)) :
    ∃ f : V →ₗ[F] F, f z = 1 ∧
      ∀ y ∈ 𝓛.lattice (i + 1 - 𝓛.period), ∃ c : O, f y = (c : F) := by
  let j := i + 1 - (𝓛.period : ℤ)
  have hji : j ≤ i := by have := 𝓛.period_pos; omega
  have hM : 𝓛.lattice (i + 1) = 𝓂[F] • 𝓛.lattice j := by
    rw [← jacobson_integer_eq_maximalIdeal, ← 𝓛.lattice_add_period]
    simp [j]
  let : (𝓛.lattice j).IsLattice F := 𝓛.isLattice j
  obtain ⟨f, a, ha, hf⟩ := exists_integral_functional (𝓛.antitone hji hz) (hM ▸ hz')
  let b : Fˣ := Units.map (algebraMap O F) a
  refine ⟨(↑b⁻¹ : F) • f, ?_, ?_⟩
  · change (↑b⁻¹ : F) * f z = 1
    rw [show f z = (b : F) from ha, Units.inv_mul]
  · intro y hy
    obtain ⟨c, hc⟩ := hf y hy
    refine ⟨(↑a⁻¹ : O) * c, ?_⟩
    change (↑b⁻¹ : F) * f y = algebraMap O F ((↑a⁻¹ : O) * c)
    rw [hc, map_mul]
    rfl

/-- Evaluation of `P^n` at a vector in `L_i \ L_{i+1}` has image `L_{i+n}`. -/
private theorem eval_filtration (𝓛 : LatticeChain O F V)
    {i : ℤ} (n : ℤ) {z : V} (hz : z ∈ 𝓛.lattice i) (hz' : z ∉ 𝓛.lattice (i + 1)) :
    (fun x : A => x z) '' (𝓛.endFiltration n : Set A) = (𝓛.lattice (i + n) : Set V) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (𝓛.mem_endFiltration.mp hx) i z hz
  · intro hy
    obtain ⟨f, hfz, hf⟩ := exists_layer_functional 𝓛 hz hz'
    exact ⟨f.smulRight y, rank_one_mem_filtration 𝓛 hf hy, by simp [hfz]⟩

/-- The integral span of the `U^0` orbit of a layer vector is its lattice. -/
private theorem span_eval_units (𝓛 : LatticeChain O F V)
    {i : ℤ} {z : V} (hz : z ∈ 𝓛.lattice i) (hz' : z ∉ 𝓛.lattice (i + 1)) :
    Submodule.span O ((fun g : G => (g : A) z) '' (𝓛.unitFiltration 0 : Set G)) =
      𝓛.lattice i := by
  let M := Submodule.span O ((fun g : G => (g : A) z) '' (𝓛.unitFiltration 0 : Set G))
  change M = _
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact 𝓛.mem_order.mp (𝓛.mem_unitFiltration_zero.mp hg).1 i z hz
  · intro y hy
    obtain ⟨f, hfz, hf⟩ := exists_layer_functional 𝓛 hz hz'
    have hji : i + 1 - (𝓛.period : ℤ) ≤ i := by have := 𝓛.period_pos; omega
    obtain ⟨c, hc⟩ := hf y (𝓛.antitone hji hy)
    let w := y - c • z
    have hw : w ∈ 𝓛.lattice i := sub_mem hy ((𝓛.lattice i).smul_mem c hz)
    have hfw : f w = 0 := by
      change f (y - c • z) = 0
      change f y = algebraMap O F c at hc
      rw [map_sub, ← algebraMap_smul F c z, map_smul, hfz, hc, smul_eq_mul, mul_one, sub_self]
    let x := f.smulRight w
    have hx : x ∈ 𝓛.order := by
      apply 𝓛.mem_order_iff_mem_endFiltration.mpr
      exact rank_one_mem_filtration 𝓛 hf (by simpa only [add_zero] using hw)
    have hxx : x * x = 0 := by
      ext v
      simp [x, Module.End.mul_apply, map_smul, hfw]
    let g : G :=
      { val := 1 + x
        inv := 1 - x
        val_inv := by
          simp only [add_mul, mul_sub, mul_one, one_mul, hxx]
          abel
        inv_val := by
          simp only [sub_mul, mul_add, mul_one, one_mul, hxx]
          abel }
    have hg : g ∈ 𝓛.unitFiltration 0 :=
      𝓛.mem_unitFiltration_zero.mpr ⟨add_mem (one_mem _) hx, sub_mem (one_mem _) hx⟩
    have hzM : z ∈ M := Submodule.subset_span ⟨1, one_mem _, by simp⟩
    have hzw : z + w ∈ M :=
      Submodule.subset_span ⟨g, hg, by simp [g, x, hfz]⟩
    have hwM : w ∈ M := by simpa [add_comm] using sub_mem hzw hzM
    simpa [w] using add_mem hwM (M.smul_mem c hzM)

private theorem stabilizer_of_conjugate_filtration (𝓛 : LatticeChain O F V)
    {g : G} {n : ℤ} (hg : conjugate g '' (𝓛.endFiltration n : Set A) = 𝓛.endFiltration n) :
    g ∈ 𝓛.stabilizer := by
  apply 𝓛.mem_stabilizer.mpr
  intro k
  obtain ⟨z, hz, hz'⟩ := exists_layer_vector 𝓛 (k - n)
  obtain ⟨j, hj, hj'⟩ := exists_layer 𝓛 (unit_apply_ne_zero_of_layer 𝓛 g hz')
  have he := image_eval_conjugate hg z
  rw [eval_filtration 𝓛 n hz hz', eval_filtration 𝓛 n hj hj', sub_add_cancel] at he
  refine ⟨j + n, SetLike.coe_injective ?_⟩
  rw [Submodule.map_coe]
  exact he

private theorem stabilizer_of_normalizes_units_zero (𝓛 : LatticeChain O F V)
    {g : G} (hg : g ∈ Subgroup.normalizer (𝓛.unitFiltration 0 : Set G)) :
    g ∈ 𝓛.stabilizer := by
  have hconj := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
  have himage : conjugate g '' ((fun u : G => (u : A)) '' (𝓛.unitFiltration 0 : Set G)) =
      (fun u : G => (u : A)) '' (𝓛.unitFiltration 0 : Set G) := by
    have he := congrArg (fun S : Set G => (fun u : G => (u : A)) '' S) hconj
    simpa only [Set.image_image, Function.comp_def, MulAut.conj_apply, Units.val_mul,
      conjugate_apply] using he
  apply 𝓛.mem_stabilizer.mpr
  intro i
  obtain ⟨z, hz, hz'⟩ := exists_layer_vector 𝓛 i
  obtain ⟨j, hj, hj'⟩ := exists_layer 𝓛 (unit_apply_ne_zero_of_layer 𝓛 g hz')
  refine ⟨j, ?_⟩
  rw [← span_eval_units 𝓛 hz hz', Submodule.map_span, ← span_eval_units 𝓛 hj hj']
  apply congrArg (Submodule.span O)
  simpa only [Set.image_image, Function.comp_def, LinearMap.restrictScalars_apply]
    using image_eval_conjugate himage z

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem conjugate_mem_filtration_of_normalizes_units (𝓛 : LatticeChain O F V)
    {n : ℕ} (hn : 1 ≤ n) {g : G} (hg : g ∈ Subgroup.normalizer (𝓛.unitFiltration n : Set G))
    {x : A} (hx : x ∈ 𝓛.endFiltration n) : conjugate g x ∈ 𝓛.endFiltration n := by
  obtain ⟨u, hu, hux⟩ := 𝓛.exists_mem_unitFiltration hn hx
  have hgu := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have h := (𝓛.mem_unitFiltration.mp hgu).2.2
  change conjugate g (u : A) - 1 ∈ 𝓛.endFiltration n at h
  rw [← map_one (conjugate g), ← map_sub, hux, add_sub_cancel_left] at h
  exact h

private theorem normalizer_units_le_stabilizer (𝓛 : LatticeChain O F V) (n : ℕ) :
    Subgroup.normalizer (𝓛.unitFiltration n : Set G) ≤ 𝓛.stabilizer := by
  intro g hg
  cases n with
  | zero => exact stabilizer_of_normalizes_units_zero 𝓛 hg
  | succ n =>
    have hn : 1 ≤ n.succ := Nat.succ_le_succ (Nat.zero_le n)
    exact stabilizer_of_conjugate_filtration 𝓛 (n := (n.succ : ℤ)) (conjugate_image_eq
      (fun _ hx => conjugate_mem_filtration_of_normalizes_units 𝓛 hn hg hx)
      (fun _ hx => conjugate_mem_filtration_of_normalizes_units 𝓛 hn (inv_mem hg) hx))

end LatticeRecovery

private theorem units_le_stabilizer (𝓛 : LatticeChain O F V) (n : ℕ) :
    𝓛.unitFiltration n ≤ 𝓛.stabilizer := by
  intro g hg
  obtain ⟨hg, hgi, _⟩ := 𝓛.mem_unitFiltration.mp hg
  apply 𝓛.mem_stabilizer.mpr
  intro i
  refine ⟨i, le_antisymm ?_ ?_⟩
  · exact Submodule.map_le_iff_le_comap.mpr fun z hz => 𝓛.mem_order.mp hg i z hz
  · intro z hz
    exact Submodule.mem_map.mpr
      ⟨(↑g⁻¹ : A) z, 𝓛.mem_order.mp hgi i z hz, by simp [← Module.End.mul_apply]⟩

private theorem stabilizer_mem_filtration (𝓛 : LatticeChain O F V) (g : 𝓛.stabilizer) :
    let g₀ : G := g
    let d := 𝓛.stabilizerValuation g
    (g₀ : A) ∈ 𝓛.endFiltration d ∧ (↑g₀⁻¹ : A) ∈ 𝓛.endFiltration (-d) := by
  intro g₀ d
  refine ⟨𝓛.mem_endFiltration.mpr ?_, 𝓛.mem_endFiltration.mpr ?_⟩
  · intro i z hz
    rw [← 𝓛.map_lattice_stabilizer g i]
    exact Submodule.mem_map_of_mem hz
  · intro i z hz
    have h := 𝓛.map_lattice_stabilizer g (i - d)
    change (𝓛.lattice (i - d)).map ((g₀ : A).restrictScalars O) = 𝓛.lattice (i - d + d) at h
    rw [sub_add_cancel] at h
    rw [← h] at hz
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hz
    change (g₀ : A) y = z at he
    rw [← he, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, ← sub_eq_add_neg]
    exact hy

private theorem conjugate_mem_filtration_of_stabilizer (𝓛 : LatticeChain O F V)
    {g : G} (hg : g ∈ 𝓛.stabilizer) {n : ℤ} {x : A} (hx : x ∈ 𝓛.endFiltration n) :
    conjugate g x ∈ 𝓛.endFiltration n := by
  obtain ⟨hg', hgi⟩ := stabilizer_mem_filtration 𝓛 ⟨g, hg⟩
  have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hg' hx) hgi
  let d := 𝓛.stabilizerValuation ⟨g, hg⟩
  change (g : A) * x * (↑g⁻¹ : A) ∈ 𝓛.endFiltration (d + n + -d) at h
  rwa [show d + n + -d = n by omega, ← conjugate_apply] at h

private theorem conjugate_mem_units_of_stabilizer (𝓛 : LatticeChain O F V)
    {g : G} (hg : g ∈ 𝓛.stabilizer) {n : ℕ} {a : G} (ha : a ∈ 𝓛.unitFiltration n) :
    g * a * g⁻¹ ∈ 𝓛.unitFiltration n := by
  obtain ⟨ha, hai, ha₁⟩ := 𝓛.mem_unitFiltration.mp ha
  refine 𝓛.mem_unitFiltration.mpr ⟨?_, ?_, ?_⟩
  · have h := conjugate_mem_filtration_of_stabilizer 𝓛 hg
      (𝓛.mem_order_iff_mem_endFiltration.mp ha)
    simpa only [conjugate_apply, Units.val_mul, 𝓛.mem_order_iff_mem_endFiltration] using h
  · have h := conjugate_mem_filtration_of_stabilizer 𝓛 hg
      (𝓛.mem_order_iff_mem_endFiltration.mp hai)
    simpa only [conjugate_apply, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc,
      𝓛.mem_order_iff_mem_endFiltration] using h
  · have h := conjugate_mem_filtration_of_stabilizer 𝓛 hg ha₁
    simpa only [map_sub, map_one, conjugate_apply, Units.val_mul] using h

private theorem stabilizer_le_normalizer_units (𝓛 : LatticeChain O F V) (n : ℕ) :
    𝓛.stabilizer ≤ Subgroup.normalizer (𝓛.unitFiltration n : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  constructor
  · exact conjugate_mem_units_of_stabilizer 𝓛 hg
  · intro ha
    simpa [mul_assoc] using conjugate_mem_units_of_stabilizer 𝓛 (inv_mem hg) ha

private theorem stabilizer_valuation_and_translates (𝓛 : LatticeChain O F V) (g : 𝓛.stabilizer) :
    let g₀ : G := g
    let d := 𝓛.stabilizerValuation g
    𝓛.valuation (g₀ : A) = d ∧
      (fun a : A => (g₀ : A) * a) '' (𝓛.order : Set A) = (𝓛.endFiltration d : Set A) ∧
      (fun a : A => a * (g₀ : A)) '' (𝓛.order : Set A) = (𝓛.endFiltration d : Set A) := by
  intro g₀ d
  obtain ⟨hg, hgi⟩ : (g₀ : A) ∈ 𝓛.endFiltration d ∧ (↑g₀⁻¹ : A) ∈ 𝓛.endFiltration (-d) :=
    stabilizer_mem_filtration 𝓛 g
  refine ⟨?_, ?_, ?_⟩
  · have hdepth : IsGreatest {n : ℤ | (g₀ : A) ∈ 𝓛.endFiltration n} d := by
      refine ⟨hg, ?_⟩
      intro n hn
      change (g₀ : A) ∈ 𝓛.endFiltration n at hn
      apply 𝓛.strictAnti.le_iff_ge.mp
      intro z hz
      have hm := 𝓛.map_lattice_stabilizer g 0
      change (𝓛.lattice 0).map ((g₀ : A).restrictScalars O) = 𝓛.lattice (0 + d) at hm
      rw [zero_add] at hm
      rw [← hm] at hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
      simpa only [LinearMap.restrictScalars_apply, zero_add] using
        (𝓛.mem_endFiltration.mp hn) 0 y hy
    have hne : (g₀ : A) ≠ 0 := by
      obtain ⟨z, _, hz⟩ := exists_layer_vector 𝓛 0
      intro he
      apply unit_apply_ne_zero_of_layer 𝓛 g₀ hz
      rw [he, LinearMap.zero_apply]
    rw [LatticeChain.valuation, ite_eq_right hne, hdepth.csSup_eq]
  · apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, rfl⟩
      change (g₀ : A) * a ∈ 𝓛.endFiltration d
      simpa only [add_zero] using
        𝓛.mul_mem_endFiltration hg (𝓛.mem_order_iff_mem_endFiltration.mp ha)
    · intro x hx
      refine ⟨(↑g₀⁻¹ : A) * x, 𝓛.mem_order_iff_mem_endFiltration.mpr ?_, ?_⟩
      · simpa only [neg_add_cancel] using 𝓛.mul_mem_endFiltration hgi hx
      · simp [← mul_assoc]
  · apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, rfl⟩
      change a * (g₀ : A) ∈ 𝓛.endFiltration d
      simpa only [zero_add] using
        𝓛.mul_mem_endFiltration (𝓛.mem_order_iff_mem_endFiltration.mp ha) hg
    · intro x hx
      refine ⟨x * (↑g₀⁻¹ : A), 𝓛.mem_order_iff_mem_endFiltration.mpr ?_, ?_⟩
      · simpa only [add_neg_cancel] using 𝓛.mul_mem_endFiltration hx hgi
      · simp [mul_assoc]

end LocalField

/-- The lattice-chain stabilizer normalizes the order and every unit filtration subgroup.
Its shift is its filtration valuation and gives both translates of the order. -/
theorem normalizer : NormalizerStatement.{u, v} := by
  intro F _ _ _ _ V _ _ 𝓛
  refine ⟨?_, ?_, ?_, stabilizer_valuation_and_translates 𝓛⟩
  · intro n
    have h := units_le_stabilizer 𝓛 n
    exact ⟨h, (Subgroup.normal_subgroupOf_iff_le_normalizer h).mpr
      (stabilizer_le_normalizer_units 𝓛 n)⟩
  · intro g
    change g ∈ 𝓛.stabilizer ↔
      conjugate g '' (𝓛.endFiltration 0 : Set (Module.End F V)) = 𝓛.endFiltration 0
    refine ⟨fun hg => conjugate_image_eq ?_ ?_, stabilizer_of_conjugate_filtration 𝓛⟩
    · exact fun _ hx => conjugate_mem_filtration_of_stabilizer 𝓛 hg hx
    · exact fun _ hx => conjugate_mem_filtration_of_stabilizer 𝓛 (inv_mem hg) hx
  · intro n
    exact le_antisymm (normalizer_units_le_stabilizer 𝓛 n) (stabilizer_le_normalizer_units 𝓛 n)

end Langlands.BushnellKutzko
