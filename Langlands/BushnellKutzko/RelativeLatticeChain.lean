import Langlands.BushnellKutzko.SubfieldIntegers
import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.UnitFiltration
import Langlands.Galois.Local.SpectralProof
import Langlands.LocalField.FiniteExtension

/-! # Relative lattice chains for normalizing subfields -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uE uV

section SpectralIntegers

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]

/-- The spectral integer ring of a finite extension consists of the integral elements. -/
theorem isIntegral_iff_mem_spectralInteger (a : E) :
    letI := LocalField.FiniteExtension.valuativeRel F E
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E] := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalField.FiniteExtension.valuativeRel F E
  let : (LocalGalois.spectralValuation F E).Compatible :=
    Valuation.Compatible.ofValuation _
  let e := RingEquiv.subringCongr (LocalGalois.localNormedField_integer F)
  have he : IsIntegral (LocalGalois.baseIntegers F) a ↔ IsIntegral 𝒪[F] a :=
    e.isIntegral_iff (by ext y; rfl) a
  refine he.symm.trans ((LocalGalois.integral_iff_mem_spectralIntegers F E a).trans ?_)
  change LocalGalois.spectralValuation F E a ≤ 1 ↔ ValuativeRel.valuation E a ≤ 1
  rw [← map_one (LocalGalois.spectralValuation F E), ← map_one (ValuativeRel.valuation E),
    ← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]

end SpectralIntegers

namespace LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  (L : LatticeChain 𝒪[F] F V)

section ScalarShift

variable (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)

private def scalarShift (a : Eˣ) : ℤ :=
  L.stabilizerValuation ⟨subfieldUnits F E V a, hE a⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hE in
private theorem smul_mem_lattice_iff (a : Eˣ) (i : ℤ) (v : V) :
    (a : E) • v ∈ L.lattice (i + L.scalarShift hE a) ↔ v ∈ L.lattice i := by
  rw [scalarShift, ← L.map_lattice_stabilizer ⟨subfieldUnits F E V a, hE a⟩,
    Submodule.mem_map]
  change (∃ w ∈ L.lattice i, (a : E) • w = (a : E) • v) ↔ _
  exact ⟨fun ⟨w, hw, he⟩ => (smul_right_injective V a.ne_zero he) ▸ hw,
    fun hv => ⟨v, hv, rfl⟩⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalarShift_one : L.scalarShift hE (1 : Eˣ) = 0 := by
  symm
  apply L.stabilizerValuation_unique _ (i := 0)
  change (L.lattice 0).map
    (((subfieldUnits F E V 1 : (Module.End F V)ˣ) : Module.End F V).restrictScalars 𝒪[F]) =
    L.lattice (0 + 0)
  rw [map_one, Units.val_one]
  exact Submodule.map_id (L.lattice 0)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalarShift_mul (a b : Eˣ) :
    L.scalarShift hE (a * b) = L.scalarShift hE a + L.scalarShift hE b := by
  symm
  apply L.stabilizerValuation_unique _ (i := 0)
  change (L.lattice 0).map
    (((subfieldUnits F E V (a * b) : (Module.End F V)ˣ) :
      Module.End F V).restrictScalars 𝒪[F]) = _
  rw [map_mul, Units.val_mul, Module.End.mul_eq_comp, LinearMap.restrictScalars_comp,
    Submodule.map_comp]
  rw [show (L.lattice 0).map
        (((subfieldUnits F E V b : (Module.End F V)ˣ) :
          Module.End F V).restrictScalars 𝒪[F]) = L.lattice (0 + L.scalarShift hE b)
    from L.map_lattice_stabilizer ⟨subfieldUnits F E V b, hE b⟩ 0]
  rw [show (L.lattice (0 + L.scalarShift hE b)).map
        (((subfieldUnits F E V a : (Module.End F V)ˣ) :
          Module.End F V).restrictScalars 𝒪[F]) =
      L.lattice (0 + L.scalarShift hE b + L.scalarShift hE a)
    from L.map_lattice_stabilizer ⟨subfieldUnits F E V a, hE a⟩ _]
  congr 1
  omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalarShift_pow (a : Eˣ) (n : ℕ) :
    L.scalarShift hE (a ^ n) = (n : ℤ) * L.scalarShift hE a := by
  induction n with
  | zero => simp [L.scalarShift_one hE]
  | succ n ih =>
    rw [pow_succ, L.scalarShift_mul hE, ih, Nat.cast_succ, add_mul, one_mul]

private theorem scalarShift_nonneg_of_integral (a : Eˣ) (ha : IsIntegral 𝒪[F] (a : E)) :
    0 ≤ L.scalarShift hE a := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨v, _, hv'⟩ := SetLike.exists_of_lt (L.lattice_succ_lt 0)
  let : IsScalarTower 𝒪[F] E V := IsScalarTower.to₁₃₄ 𝒪[F] F E V
  let C := Algebra.adjoin 𝒪[F] ({(a : E)} : Set E)
  let : Module.Finite 𝒪[F] C := Algebra.finite_adjoin_simple_of_isIntegral ha
  let f : C →ₗ[𝒪[F]] V :=
    { toFun := fun c => (c : E) • v
      map_add' := fun x y => add_smul (x : E) (y : E) v
      map_smul' := fun c x => smul_assoc c (x : E) v }
  obtain ⟨s, hs⟩ := Submodule.fg_range f
  obtain ⟨i, hi⟩ := L.exists_forall_finset_mem hπ s
  have hle : f.range ≤ L.lattice i := by
    rw [← hs, Submodule.span_le]
    exact hi
  have hpow (n : ℕ) : (a : E) ^ n • v ∈ L.lattice i := by
    let ac : C := ⟨a, Algebra.subset_adjoin (Set.mem_singleton _)⟩
    exact hle (LinearMap.mem_range.mpr ⟨ac ^ n, rfl⟩)
  by_contra hn
  let n := (1 - i).toNat
  have hdeep : 1 ≤ i - (n : ℤ) * L.scalarShift hE a := by
    have h : (n : ℤ) * L.scalarShift hE a ≤ -(n : ℤ) := by
      simpa using mul_le_mul_of_nonneg_left (show L.scalarShift hE a ≤ -1 by omega)
        (show 0 ≤ (n : ℤ) by exact_mod_cast Nat.zero_le n)
    dsimp [n] at *
    omega
  let j := i - (n : ℤ) * L.scalarShift hE a
  have hj : j + L.scalarShift hE (a ^ n) = i := by
    rw [L.scalarShift_pow hE]
    dsimp [j]
    omega
  have hm : (↑(a ^ n) : E) • v ∈ L.lattice (j + L.scalarShift hE (a ^ n)) := by
    rw [hj, Units.val_pow_eq_pow_val]
    exact hpow n
  exact hv' (L.antitone hdeep ((L.smul_mem_lattice_iff hE (a ^ n) j v).mp hm))

end ScalarShift

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
  (hInt : ∀ a : E, IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E])

private abbrev relativeIntegerUnits : 𝒪[E]ˣ →* Eˣ := Units.map (algebraMap 𝒪[E] E)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
include hE hInt in
private theorem scalarShift_relativeIntegerUnit (a : 𝒪[E]ˣ) :
    L.scalarShift hE (relativeIntegerUnits a) = 0 := by
  have ha : 0 ≤ L.scalarShift hE (relativeIntegerUnits a) :=
    L.scalarShift_nonneg_of_integral hE _ ((hInt _).mpr (a : 𝒪[E]).property)
  have ha' : 0 ≤ L.scalarShift hE (relativeIntegerUnits a⁻¹) :=
    L.scalarShift_nonneg_of_integral hE _ ((hInt _).mpr ((a⁻¹ : 𝒪[E]ˣ) : 𝒪[E]).property)
  have hadd := L.scalarShift_mul hE (relativeIntegerUnits a) (relativeIntegerUnits a⁻¹)
  rw [← map_mul, mul_inv_cancel, map_one, L.scalarShift_one hE] at hadd
  omega

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
include hE hInt in
private theorem relativeInteger_smul_mem_lattice (a : 𝒪[E]) {i : ℤ} {v : V}
    (hv : v ∈ L.lattice i) : (a : E) • v ∈ L.lattice i := by
  by_cases ha : (a : E) = 0
  · simp [ha]
  let u := Units.mk0 (a : E) ha
  have hnonneg := L.scalarShift_nonneg_of_integral hE u ((hInt _).mpr a.property)
  exact L.antitone (show i ≤ i + L.scalarShift hE u by omega)
    ((L.smul_mem_lattice_iff hE u i v).mpr hv)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
include hInt in
private theorem baseInteger_mem_relativeIntegers (a : 𝒪[F]) : algebraMap F E (a : F) ∈ 𝒪[E] :=
  (hInt _).mp (by
    change IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a)
    exact isIntegral_algebraMap)

include hE hInt in
private theorem scalarShift_relativeUniformizer_pos {π : 𝒪[E]} (hπ : Irreducible π) :
    0 < L.scalarShift hE (uniformizerAsUnit hπ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let u := Units.map (algebraMap F E).toMonoidHom (uniformizerAsUnit hϖ)
  have he : (u : E) = algebraMap F E (ϖ : F) := rfl
  have hp : (L.period : ℤ) = L.scalarShift hE u := by
    apply L.stabilizerValuation_unique ⟨subfieldUnits F E V u, hE u⟩ (i := 0)
    ext v
    change (∃ w ∈ L.lattice 0, (u : E) • w = v) ↔ v ∈ L.lattice (0 + L.period)
    rw [L.lattice_add_period, jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp only [he, algebraMap_smul, Subring.smul_def]
  obtain ⟨n, w, hw⟩ := exists_eq_pow_mul_unit_of_mem hπ u.ne_zero
    (he ▸ baseInteger_mem_relativeIntegers hInt ϖ)
  have hu : u = uniformizerAsUnit hπ ^ n * relativeIntegerUnits w := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_uniformizerAsUnit, Units.coe_map]
    exact hw)
  rw [hu, L.scalarShift_mul hE, L.scalarShift_pow hE, L.scalarShift_relativeIntegerUnit hE hInt,
    add_zero] at hp
  have hpos : 0 < (L.period : ℤ) := by exact_mod_cast L.period_pos
  rw [hp] at hpos
  exact pos_of_mul_pos_right hpos (by exact_mod_cast Nat.zero_le n)

/-- A lattice of a chain normalized by `Eˣ` with scalars in the integers of `E`. -/
private def relativeLattice (i : ℤ) : Submodule 𝒪[E] V where
  carrier := L.lattice i
  add_mem' := (L.lattice i).add_mem'
  zero_mem' := (L.lattice i).zero_mem'
  smul_mem' := fun a _ hv => L.relativeInteger_smul_mem_lattice hE hInt a (i := i) hv

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem isLattice_relativeLattice (i : ℤ) : (L.relativeLattice hE hInt i).IsLattice E where
  fg := by
    classical
    obtain ⟨s, hs⟩ := (L.isLattice i).fg
    refine ⟨s, le_antisymm (Submodule.span_le.mpr fun v hv =>
      show v ∈ L.lattice i from hs ▸ Submodule.subset_span hv) ?_⟩
    intro v hv
    have hv' : v ∈ Submodule.span 𝒪[F] (s : Set V) := hs.symm ▸ hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx =>
      let a' : 𝒪[E] := ⟨algebraMap F E (a : F), baseInteger_mem_relativeIntegers hInt a⟩
      have he : a' • x = a • x := by
        change (algebraMap F E (a : F)) • x = a • x
        rw [algebraMap_smul, Subring.smul_def]
      exact he ▸ Submodule.smul_mem _ a' hx
  span_eq_top := by
    change Submodule.span E (L.lattice i : Set V) = ⊤
    have h := Submodule.span_le_restrictScalars F E (L.lattice i : Set V)
    rw [(L.isLattice i).span_eq_top] at h
    exact eq_top_iff.2 (fun v _ => h (Submodule.mem_top (x := v)))

/-- A chain normalized by `Eˣ` is a lattice chain over `E` with the same lattice subsets. -/
def relativeLatticeChain : LatticeChain 𝒪[E] E V where
  lattice := L.relativeLattice hE hInt
  isLattice := L.isLattice_relativeLattice hE hInt
  lattice_succ_lt i := by
    refine lt_of_le_not_ge (L.lattice_succ_lt i).le ?_
    exact (L.lattice_succ_lt i).not_ge
  exists_period := by
    classical
    let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[E])
    have hπ : Irreducible π :=
      Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[E])
    let e := L.scalarShift hE (uniformizerAsUnit hπ)
    have hpos : 0 < e := L.scalarShift_relativeUniformizer_pos hE hInt hπ
    refine ⟨e.toNat, by omega, fun i => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le, jacobson_integer_eq_maximalIdeal, hπ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul]
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change v ∈ L.lattice (i + e) ↔ ∃ w ∈ L.lattice i, (uniformizerAsUnit hπ : E) • w = v
    rw [show L.lattice (i + e) = (L.lattice i).map
        (((subfieldUnits F E V (uniformizerAsUnit hπ) : (Module.End F V)ˣ) :
          Module.End F V).restrictScalars 𝒪[F])
      from (L.map_lattice_stabilizer ⟨_, hE _⟩ i).symm]
    rfl

@[simp]
theorem mem_relativeLatticeChain (i : ℤ) (v : V) :
    v ∈ (L.relativeLatticeChain hE hInt).lattice i ↔ v ∈ L.lattice i := Iff.rfl

theorem mem_relativeLatticeChain_endFiltration (i : ℤ) (x : Module.End E V) :
    x ∈ (L.relativeLatticeChain hE hInt).endFiltration i ↔
      x.restrictScalars F ∈ L.endFiltration i := Iff.rfl

end LatticeChain

end Langlands.BushnellKutzko
