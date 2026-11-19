import Langlands.BushnellKutzko.UnitFiltration

/-! # Successive quotients of a lattice chain -/

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- The submodule of `L_i` consisting of vectors in `L_j`. -/
abbrev intervalSubmodule (i j : ℤ) : Submodule O (𝓛.lattice i) :=
  (𝓛.lattice j).comap (𝓛.lattice i).subtype

/-- The quotient `L_i / L_j` when `i ≤ j`. -/
abbrev Interval (i j : ℤ) := (𝓛.lattice i) ⧸ 𝓛.intervalSubmodule i j

/-- The successive quotient `L_i / L_{i+1}`. -/
abbrev Layer (i : ℤ) := 𝓛.Interval i (i + 1)

/-- The class of a vector of `L_i` in the quotient by `L_j`. -/
def intervalMk (i j : ℤ) (v : V) (hv : v ∈ 𝓛.lattice i) : 𝓛.Interval i j :=
  Submodule.Quotient.mk ⟨v, hv⟩

theorem intervalMk_surjective (i j : ℤ) (q : 𝓛.Interval i j) :
    ∃ (v : V) (hv : v ∈ 𝓛.lattice i), 𝓛.intervalMk i j v hv = q := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨v, hv, rfl⟩

@[simp] theorem intervalMk_eq_iff {i j : ℤ} {v w : V}
    (hv : v ∈ 𝓛.lattice i) (hw : w ∈ 𝓛.lattice i) :
    𝓛.intervalMk i j v hv = 𝓛.intervalMk i j w hw ↔ v - w ∈ 𝓛.lattice j :=
  Submodule.Quotient.eq _

@[simp] theorem intervalMk_eq_zero_iff {i j : ℤ} {v : V} (hv : v ∈ 𝓛.lattice i) :
    𝓛.intervalMk i j v hv = 0 ↔ v ∈ 𝓛.lattice j :=
  Submodule.Quotient.mk_eq_zero _

/-- A map preserving the two relevant inclusions induces a map on their quotients. -/
def intervalMap {i j k l : ℤ} (f : V →ₗ[O] V)
    (hi : Set.MapsTo f (𝓛.lattice i) (𝓛.lattice k))
    (hj : Set.MapsTo f (𝓛.lattice j) (𝓛.lattice l)) :
    𝓛.Interval i j →ₗ[O] 𝓛.Interval k l :=
  (𝓛.intervalSubmodule i j).mapQ (𝓛.intervalSubmodule k l)
    ((f.domRestrict (𝓛.lattice i)).codRestrict (𝓛.lattice k) (fun v => hi v.2))
    (fun _ hv => hj hv)

@[simp] theorem intervalMap_mk {i j k l : ℤ} (f : V →ₗ[O] V)
    (hi : Set.MapsTo f (𝓛.lattice i) (𝓛.lattice k))
    (hj : Set.MapsTo f (𝓛.lattice j) (𝓛.lattice l)) (v : V) (hv : v ∈ 𝓛.lattice i) :
    𝓛.intervalMap f hi hj (𝓛.intervalMk i j v hv) = 𝓛.intervalMk k l (f v) (hi hv) :=
  rfl

/-- Strict decrease makes every successive quotient nonzero. -/
theorem layer_nontrivial (i : ℤ) : Nontrivial (𝓛.Layer i) := by
  obtain ⟨v, hv, hnv⟩ := (SetLike.lt_iff_le_and_exists.mp (𝓛.lattice_succ_lt i)).2
  exact ⟨⟨𝓛.intervalMk i (i + 1) v hv, 0, (𝓛.intervalMk_eq_zero_iff hv).not.mpr hnv⟩⟩

/-- Each order element acts by an endomorphism on a successive quotient. -/
def layerAction (x : 𝓛.order) (i : ℤ) : Module.End O (𝓛.Layer i) :=
  𝓛.intervalMap (x.val.restrictScalars O) (fun _ hv => (𝓛.mem_order.mp x.prop) i _ hv)
    (fun _ hv => (𝓛.mem_order.mp x.prop) (i + 1) _ hv)

@[simp] theorem layerAction_mk (x : 𝓛.order) (i : ℤ) (v : V) (hv : v ∈ 𝓛.lattice i) :
    𝓛.layerAction x i (𝓛.intervalMk i (i + 1) v hv) =
      𝓛.intervalMk i (i + 1) (x.val v) ((𝓛.mem_order.mp x.prop) i v hv) :=
  rfl

/-- Order elements act identically on every layer exactly when their difference has depth one. -/
theorem layerAction_eq_iff (x y : 𝓛.order) :
    (∀ i, 𝓛.layerAction x i = 𝓛.layerAction y i) ↔ x.val - y.val ∈ 𝓛.endFiltration 1 := by
  constructor
  · intro h i v hv
    have heq := LinearMap.congr_fun (h i) (𝓛.intervalMk i (i + 1) v hv)
    simpa only [layerAction_mk, intervalMk_eq_iff, LinearMap.sub_apply] using heq
  · intro h i
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    simpa only [layerAction_mk, intervalMk_eq_iff, LinearMap.sub_apply] using h i v hv

/-- Membership in the shifted lattice pulls back to membership in the initial lattice. -/
theorem mem_lattice_stabilizer_iff (g : 𝓛.stabilizer) (i : ℤ) (v : V) :
    (g.val : Module.End K V) v ∈ 𝓛.lattice (i + 𝓛.stabilizerValuation g) ↔
      v ∈ 𝓛.lattice i := by
  rw [← 𝓛.map_lattice_stabilizer g i]
  constructor
  · rintro ⟨w, hw, heq⟩
    have hvw := congrArg (fun z => ((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) z) heq
    change ((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((g.val : Module.End K V) w) =
      ((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((g.val : Module.End K V) v) at hvw
    simp only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at hvw
    exact hvw ▸ hw
  · exact Submodule.mem_map_of_mem

/-- A shifting unit carries a layer isomorphically onto the translated layer. -/
def stabilizerLayerEquiv (g : 𝓛.stabilizer) (i j : ℤ)
    (h : j = i + 𝓛.stabilizerValuation g) : 𝓛.Layer i ≃ₗ[O] 𝓛.Layer j := by
  have hi : Set.MapsTo (g.val : Module.End K V) (𝓛.lattice i) (𝓛.lattice j) := by
    intro v hv
    rw [h]
    exact (𝓛.mem_lattice_stabilizer_iff g i v).mpr hv
  have hj' : j + 1 = i + 1 + 𝓛.stabilizerValuation g := by omega
  have hj : Set.MapsTo (g.val : Module.End K V) (𝓛.lattice (i + 1)) (𝓛.lattice (j + 1)) := by
    intro v hv
    rw [hj']
    exact (𝓛.mem_lattice_stabilizer_iff g (i + 1) v).mpr hv
  refine LinearEquiv.ofBijective (𝓛.intervalMap ((g.val : Module.End K V).restrictScalars O) hi hj)
    ⟨?_, ?_⟩
  · intro q r heq
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    obtain ⟨w, hw, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) r
    change 𝓛.intervalMk j (j + 1) ((g.val : Module.End K V) v) (hi hv) =
      𝓛.intervalMk j (j + 1) ((g.val : Module.End K V) w) (hi hw) at heq
    rw [intervalMk_eq_iff] at heq
    rw [← map_sub, hj'] at heq
    exact (𝓛.intervalMk_eq_iff hv hw).mpr ((𝓛.mem_lattice_stabilizer_iff g (i + 1) _).mp heq)
  · intro q
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective j (j + 1) q
    let w := ((g.val⁻¹ : (Module.End K V)ˣ) : Module.End K V) v
    have hwv : (g.val : Module.End K V) w = v := by
      simp only [w, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have hw : w ∈ 𝓛.lattice i := (𝓛.mem_lattice_stabilizer_iff g i w).mp (by rwa [hwv, ← h])
    refine ⟨𝓛.intervalMk i (i + 1) w hw, ?_⟩
    change 𝓛.intervalMk j (j + 1) ((g.val : Module.End K V) w) (hi hw) =
      𝓛.intervalMk j (j + 1) v hv
    rw [intervalMk_eq_iff, hwv, sub_self]
    exact (𝓛.lattice (j + 1)).zero_mem

@[simp] theorem stabilizerLayerEquiv_mk (g : 𝓛.stabilizer) {i j : ℤ}
    (h : j = i + 𝓛.stabilizerValuation g) (v : V) (hv : v ∈ 𝓛.lattice i) :
    𝓛.stabilizerLayerEquiv g i j h (𝓛.intervalMk i (i + 1) v hv) =
      𝓛.intervalMk j (j + 1) ((g.val : Module.End K V) v)
        (h.symm ▸ (𝓛.mem_lattice_stabilizer_iff g i v).mpr hv) :=
  rfl

section Residue

variable [IsLocalRing O]

/-- Quotients by lattices within one period are annihilated by the maximal ideal. -/
theorem interval_isTorsionBySet {i j : ℤ} (h : j ≤ i + 𝓛.period) :
    Module.IsTorsionBySet O (𝓛.Interval i j) (IsLocalRing.maximalIdeal O : Set O) := by
  apply (Module.isTorsionBySet_quotient_iff _ _).mpr
  intro v a ha
  change a • (v : V) ∈ 𝓛.lattice j
  apply 𝓛.antitone h
  rw [𝓛.lattice_add_period, IsLocalRing.ringJacobson_eq_maximalIdeal]
  exact Submodule.smul_mem_smul ha v.prop

/-- The residue scalar action on a quotient by a lattice within one period. -/
@[instance_reducible]
def intervalResidueModule {i j : ℤ} (h : j ≤ i + 𝓛.period) :
    Module (IsLocalRing.ResidueField O) (𝓛.Interval i j) :=
  (𝓛.interval_isTorsionBySet h).module

/-- The residue scalar action extends the original integer action. -/
theorem intervalResidueTower {i j : ℤ} (h : j ≤ i + 𝓛.period) :
    letI := 𝓛.intervalResidueModule h
    IsScalarTower O (IsLocalRing.ResidueField O) (𝓛.Interval i j) :=
  (𝓛.interval_isTorsionBySet h).isScalarTower

omit [IsLocalRing O] in
theorem layer_le_period (i : ℤ) : i + 1 ≤ i + (𝓛.period : ℤ) := by
  have := 𝓛.period_pos
  omega

instance layerResidueModule (i : ℤ) : Module (IsLocalRing.ResidueField O) (𝓛.Layer i) :=
  𝓛.intervalResidueModule (𝓛.layer_le_period i)

instance layerResidueTower (i : ℤ) : IsScalarTower O (IsLocalRing.ResidueField O) (𝓛.Layer i) :=
  𝓛.intervalResidueTower (𝓛.layer_le_period i)

end Residue

end Langlands.BushnellKutzko.LatticeChain
