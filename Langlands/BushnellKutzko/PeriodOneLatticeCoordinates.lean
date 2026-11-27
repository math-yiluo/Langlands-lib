import Langlands.BushnellKutzko.CuspidalMatrixIntertwining
import Langlands.BushnellKutzko.LatticeChainLayerLift
import Langlands.BushnellKutzko.LatticeChainLayerCommutation
import Langlands.BushnellKutzko.SimpleTypes
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.Module

/-! # Integral matrix coordinates of a lattice chain of period one -/

noncomputable section

open IsLocalRing
open scoped WithZero
open scoped TensorProduct

namespace Langlands.BushnellKutzko

open GeneralLinear.Iwasawa

section DiscreteValuation

variable (O K : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

/-- A discrete valuation ring is the integer ring of its height-one valuation on the
fraction field. A uniformizer realizes every nonzero value by an integer power. -/
theorem exists_fraction_valuation_integers :
    ∃ (v : Valuation K ℤᵐ⁰) (ϖ : Kˣ), v.Integers O ∧ IsUniformizingElement v ϖ := by
  let p := IsDiscreteValuationRing.maximalIdeal O
  let v := p.valuation K
  have hv : v.Integers O :=
    ⟨IsFractionRing.injective O K, p.valuation_le_one (K := K),
      fun _ hx => IsDiscreteValuationRing.exists_lift_of_le_one hx⟩
  obtain ⟨a, ha⟩ := p.valuation_exists_uniformizer K
  have ha' : v a = WithZero.exp (-1) := ha
  have ha₀ : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha'
    exact WithZero.exp_ne_zero ha'.symm
  refine ⟨v, Units.mk0 a ha₀, hv, ?_, fun x hx => ?_⟩
  · change v a < 1
    rw [ha', WithZero.exp_lt_one_iff]
    norm_num
  · refine ⟨-WithZero.log (v x), ?_⟩
    change v x = v a ^ (-WithZero.log (v x))
    rw [ha', ← WithZero.exp_zsmul]
    simp [WithZero.exp_log ((v.ne_zero_iff).2 hx)]

end DiscreteValuation

namespace LatticeChain

variable {O K V : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module O V] [Module K V]
  [IsScalarTower O K V] (L : LatticeChain O K V)

omit [IsFractionRing O K] in
private theorem layerZero_submodule_eq (hL : L.period = 1) :
    L.intervalSubmodule 0 (0 + 1) = maximalIdeal O • (⊤ : Submodule O (L.lattice 0)) := by
  apply Submodule.map_injective_of_injective (L.lattice 0).injective_subtype
  rw [intervalSubmodule, Submodule.map_comap_eq, Submodule.map_smul'', Submodule.map_top,
    Submodule.range_subtype, inf_eq_right.mpr (L.antitone (by omega))]
  simpa only [hL, Nat.cast_one, ringJacobson_eq_maximalIdeal] using L.lattice_add_period 0

/-- The prescribed basis of the zeroth graded piece of a period-one chain lifts to a basis of
its zeroth lattice. -/
theorem exists_basis_lift_layerZero (hL : L.period = 1) {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField O) (L.Layer 0)) :
    ∃ a : Module.Basis (Fin n) O (L.lattice 0),
      ∀ j, L.intervalMk 0 (0 + 1) (a j) (a j).2 = b j := by
  let M := L.lattice 0
  let eO : (ResidueField O ⊗[O] M) ≃ₗ[O] L.Layer 0 :=
    (TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal O)).trans
      (Submodule.quotEquivOfEq _ _ (L.layerZero_submodule_eq hL).symm)
  let e := eO.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := O))
  have he (x : M) : e (1 ⊗ₜ[O] x) = L.intervalMk 0 (0 + 1) x x.2 := by
    change Submodule.quotEquivOfEq _ _ (L.layerZero_submodule_eq hL).symm
      (TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal O)
        ((1 : O ⧸ maximalIdeal O) ⊗ₜ[O] x)) = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.quotEquivOfEq_mk]
    rfl
  choose a ha ha' using fun j => L.intervalMk_surjective 0 (0 + 1) (b j)
  let w (j : Fin n) : M := ⟨a j, ha j⟩
  let d := b.map e.symm
  have hd : TensorProduct.mk O (ResidueField O) M 1 ∘ w = d :=
    funext fun j => e.injective (by simpa only [d, Function.comp_apply, Module.Basis.map_apply,
      TensorProduct.mk_apply, he, LinearEquiv.apply_symm_apply] using ha' j)
  have : Module.Finite O M := Module.Finite.iff_fg.2 (L.fg_lattice 0)
  have : M.IsLattice K := L.isLattice 0
  have : Module.IsTorsionFree O K := Module.IsTorsionFree.trans_faithfulSMul O K K
  have bij : Function.Bijective (Finsupp.linearCombination O w) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [hd, ← d.coe_repr_symm]
    exact d.repr.symm.bijective
  let a' : Module.Basis (Fin n) O M :=
    ⟨(LinearEquiv.ofBijective (Finsupp.linearCombination O w) bij).symm⟩
  have ha'₁ (j : Fin n) : a' j = w j := by
    rw [← a'.repr_symm_single_one]
    exact (Finsupp.linearCombination_single O (v := w) 1 j).trans (one_smul _ _)
  exact ⟨a', fun j => by simpa only [ha'₁] using ha' j⟩

/-- For a chain of period one, preserving its zeroth lattice implies preserving every
lattice, since the others are its translates by powers of a scalar uniformizer. -/
theorem mem_order_iff_preserves_latticeZero (hL : L.period = 1) (x : Module.End K V) :
    x ∈ L.order ↔ Set.MapsTo x (L.lattice 0) (L.lattice 0) := by
  refine ⟨fun hx _ hv => (L.mem_order.1 hx) 0 _ hv, fun hx => L.mem_order.2 ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let p := L.uniformizerStabilizer hπ
  let sh : L.stabilizer →* Multiplicative ℤ :=
    ⟨⟨fun g => Multiplicative.ofAdd (L.stabilizerValuation g), by simp⟩,
      fun g h => congrArg Multiplicative.ofAdd (L.stabilizerValuation_mul g h)⟩
  have hs (i : ℤ) : L.stabilizerValuation (p ^ i) = i := by
    have h := congrArg Multiplicative.toAdd (map_zpow sh p i)
    change L.stabilizerValuation (p ^ i) = ((sh p) ^ i).toAdd at h
    change L.stabilizerValuation (p ^ i) = i • L.stabilizerValuation p at h
    simpa [p, hL] using h
  have hc (i : ℤ) : Commute x (((p ^ i : L.stabilizer) : (Module.End K V)ˣ) : Module.End K V) := by
    let πu := Units.mk0 (algebraMap O K π) ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hπ.ne_zero)
    let f := (algebraMap K (Module.End K V)).toMonoidHom
    have hp : p.val = Units.map f πu := rfl
    rw [Subgroup.coe_zpow, hp, ← map_zpow]
    ext v
    change x (((πu ^ i : Kˣ) : K) • v) = ((πu ^ i : Kˣ) : K) • x v
    rw [map_smul]
  intro i v hv
  let u := ((p ^ i : L.stabilizer) : (Module.End K V)ˣ)
  have hm := L.map_lattice_stabilizer (p ^ i) 0
  rw [hs, zero_add] at hm
  change (L.lattice 0).map ((u : Module.End K V).restrictScalars O) = L.lattice i at hm
  rw [← hm] at hv ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
  refine Submodule.mem_map.2 ⟨x w, hx hw, ?_⟩
  exact (congrArg (fun y : Module.End K V => y w) (hc i).eq).symm

section Coordinates

variable {n : ℕ} (a : Module.Basis (Fin n) O (L.lattice 0))

/-- The fraction-field basis extending an integral basis of the zeroth lattice. -/
def extendedBasis : Module.Basis (Fin n) K V :=
  letI := L.isLattice 0
  letI : Module.IsTorsionFree O K := Module.IsTorsionFree.trans_faithfulSMul O K K
  a.extendOfIsLattice K

@[simp] theorem extendedBasis_apply (j : Fin n) : L.extendedBasis a j = (a j : V) := by
  let := L.isLattice 0
  let : Module.IsTorsionFree O K := Module.IsTorsionFree.trans_faithfulSMul O K K
  exact a.extendOfIsLattice_apply K j

/-- Matrix coordinates for the ambient group. -/
def matrixEquiv : (Module.End K V)ˣ ≃* GeneralLinear n K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv (L.extendedBasis a)).toMulEquiv

private theorem extendedBasis_coord_lattice (y : L.lattice 0) (i : Fin n) :
    (L.extendedBasis a).repr (y : V) i = algebraMap O K (a.repr y i) := by
  let g := ((L.extendedBasis a).coord i).restrictScalars O ∘ₗ (L.lattice 0).subtype
  let f := (Algebra.linearMap O K) ∘ₗ a.coord i
  have h : g = f := by
    apply a.ext
    intro j
    change (L.extendedBasis a).repr (a j : V) i = algebraMap O K (a.repr (a j) i)
    rw [← L.extendedBasis_apply]
    simp only [Module.Basis.repr_self_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h y

private theorem mem_latticeZero_iff_entries (y : V) :
    y ∈ L.lattice 0 ↔ ∀ i, (L.extendedBasis a).repr y i ∈ (algebraMap O K).range := by
  constructor
  · intro hy i
    exact ⟨a.repr ⟨y, hy⟩ i, (L.extendedBasis_coord_lattice a ⟨y, hy⟩ i).symm⟩
  · intro hy
    choose c hc using hy
    let z := a.equivFun.symm c
    have hz : (z : V) = y := by
      apply (L.extendedBasis a).ext_elem_iff.2
      intro i
      rw [L.extendedBasis_coord_lattice a, ← Module.Basis.equivFun_apply]
      simpa only [z, LinearEquiv.apply_symm_apply] using hc i
    exact hz ▸ z.2

private theorem end_preserves_zero_iff_entries (x : Module.End K V) :
    Set.MapsTo x (L.lattice 0) (L.lattice 0) ↔
      ∀ i j, LinearMap.toMatrixAlgEquiv (L.extendedBasis a) x i j ∈ (algebraMap O K).range := by
  simp only [LinearMap.toMatrixAlgEquiv_apply]
  constructor
  · intro hx i j
    apply (L.mem_latticeZero_iff_entries a _).1 _ i
    rw [L.extendedBasis_apply]
    exact hx (a j).2
  · intro hx v hv
    let f := x.restrictScalars O ∘ₗ (L.lattice 0).subtype
    have hr : LinearMap.range f ≤ L.lattice 0 := by
      rw [← Submodule.map_top, ← a.span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      apply (L.mem_latticeZero_iff_entries a _).2
      intro i
      simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, L.extendedBasis_apply] using hx i j
    exact hr ⟨⟨v, hv⟩, rfl⟩

/-- In an integral basis the period-one lattice unit subgroup is the integral matrix subgroup. -/
theorem matrixEquiv_mem_integral_iff (hL : L.period = 1) (x : (Module.End K V)ˣ) :
    L.matrixEquiv a x ∈ IntegralMatrices.subgroup O K n ↔ x ∈ L.unitFiltration 0 := by
  rw [IntegralMatrices.mem_subgroup_iff (IsFractionRing.injective O K), L.mem_unitFiltration_zero,
    L.mem_order_iff_preserves_latticeZero hL, L.mem_order_iff_preserves_latticeZero hL,
    L.end_preserves_zero_iff_entries a, L.end_preserves_zero_iff_entries a,
    ← map_inv (L.matrixEquiv a)]
  rfl

/-- Matrix coordinates on the lattice unit subgroup. -/
def latticeMatrixEquiv (hL : L.period = 1) : L.unitFiltration 0 ≃* IntegralMatrices.subgroup O K n :=
  ((L.unitFiltration 0).equivMapOfInjective (L.matrixEquiv a).toMonoidHom
    (L.matrixEquiv a).injective).trans (MulEquiv.subgroupCongr (by
      ext y
      obtain ⟨x, rfl⟩ := (L.matrixEquiv a).surjective y
      exact ⟨fun ⟨w, hw, he⟩ => (L.matrixEquiv_mem_integral_iff a hL x).2
        ((L.matrixEquiv a).injective he ▸ hw),
        fun hy => ⟨x, (L.matrixEquiv_mem_integral_iff a hL x).1 hy, rfl⟩⟩))

@[simp] theorem coe_latticeMatrixEquiv (hL : L.period = 1) (u : L.unitFiltration 0) :
    (L.latticeMatrixEquiv a hL u : GeneralLinear n K) = L.matrixEquiv a u := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- A scalar automorphism becomes a scalar matrix. -/
theorem matrixEquiv_scalar (u : Kˣ) :
    L.matrixEquiv a (Units.map (algebraMap K (Module.End K V)).toMonoidHom u) =
      GeneralLinear.scalar u := by
  apply Units.ext
  ext i j
  change LinearMap.toMatrixAlgEquiv (L.extendedBasis a) (algebraMap K (Module.End K V) u.val) i j = _
  rw [(LinearMap.toMatrixAlgEquiv (L.extendedBasis a)).commutes]
  rfl

omit [IsFractionRing O K] in
private theorem layerZero_coord (b : Module.Basis (Fin n) (ResidueField O) (L.Layer 0))
    (ha : ∀ j, L.intervalMk 0 (0 + 1) (a j) (a j).2 = b j)
    (x : L.lattice 0) (i : Fin n) :
    b.equivFun (L.intervalMk 0 (0 + 1) x x.2) i = residue O (a.repr x i) := by
  let f := (b.coord i).restrictScalars O ∘ₗ (L.intervalSubmodule 0 (0 + 1)).mkQ
  let g := Algebra.linearMap O (ResidueField O) ∘ₗ a.coord i
  have h : f = g := by
    apply a.ext
    intro j
    change b.repr (L.intervalMk 0 (0 + 1) (a j) (a j).2) i = residue O (a.repr (a j) i)
    rw [ha]
    simp only [Module.Basis.repr_self_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h x

/-- The prescribed layer action in a lifted basis is entrywise residue reduction of the
integral matrix of the automorphism. -/
theorem layerReduction_eq_matrix_reduction (hL : L.period = 1)
    (b : ∀ i : Fin 1, Module.Basis (Fin n) (ResidueField O) (L.Layer ((i : ℕ) : ℤ)))
    (ha : ∀ j, L.intervalMk 0 (0 + 1) (a j) (a j).2 = b 0 j)
    (φ : L.unitFiltration 0 →* (Fin 1 → GeneralLinear n (ResidueField O)))
    (hφ : IsLayerReduction L (L.unitFiltration 0)
      (fun _ hu i _ hv => L.apply_mem_lattice_of_mem_unitFiltration hu i hv) b φ) :
    (Pi.evalMonoidHom _ 0).comp φ =
      (IntegralMatrices.reduction (IsFractionRing.injective O K)).comp
        (L.latticeMatrixEquiv a hL).toMonoidHom := by
  ext u : 1
  apply Units.ext
  ext i j
  let z := L.latticeMatrixEquiv a hL u
  let g := IntegralMatrices.equivSubgroup (n := n) (IsFractionRing.injective O K)
  let zO := g.symm z
  let x : L.lattice 0 := ⟨(u.val : Module.End K V) (a j),
    L.apply_mem_lattice_of_mem_unitFiltration u.2 0 (a j).2⟩
  have he : Matrix.GeneralLinearGroup.map (algebraMap O K) zO = L.matrixEquiv a u := by
    exact congrArg Subtype.val (g.apply_symm_apply z)
  have hentry := congrArg (fun m : GeneralLinear n K => m i j) he
  change algebraMap O K (zO i j) =
    LinearMap.toMatrixAlgEquiv (L.extendedBasis a) (u.val : Module.End K V) i j at hentry
  rw [LinearMap.toMatrixAlgEquiv_apply, L.extendedBasis_apply] at hentry
  change algebraMap O K (zO i j) = (L.extendedBasis a).repr (x : V) i at hentry
  rw [L.extendedBasis_coord_lattice a] at hentry
  have hentry' := IsFractionRing.injective O K hentry
  have hact := congrFun (hφ u 0 (a j) (a j).2) i
  change ((b 0).equivFun (L.intervalMk 0 (0 + 1) x x.2)) i =
    Matrix.mulVec (φ u 0).val ((b 0).equivFun (L.intervalMk 0 (0 + 1) (a j) (a j).2)) i at hact
  have hb : (b 0).equivFun (b 0 j) = Pi.single j 1 := by
    funext k
    simp only [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : j = k <;> simp [h, eq_comm]
  rw [L.layerZero_coord a (b 0) ha, ha, hb, Matrix.mulVec_single_one, Matrix.col_apply] at hact
  change (φ u 0) i j = residue O (zO i j)
  rw [hentry']
  exact hact.symm

end Coordinates

/-- A period-one layer reduction is onto the single residue-field factor. -/
theorem layerReduction_surjective_periodOne (hL : L.period = 1) {n : ℕ}
    (b : ∀ i : Fin 1, Module.Basis (Fin n) (ResidueField O) (L.Layer ((i : ℕ) : ℤ)))
    (φ : L.unitFiltration 0 →* (Fin 1 → GeneralLinear n (ResidueField O)))
    (hφ : IsLayerReduction L (L.unitFiltration 0)
      (fun _ hu i _ hv => L.apply_mem_lattice_of_mem_unitFiltration hu i hv) b φ) :
    Function.Surjective ((Pi.evalMonoidHom _ (0 : Fin 1)).comp φ) := by
  obtain ⟨a, ha⟩ := L.exists_basis_lift_layerZero hL (b 0)
  rw [L.layerReduction_eq_matrix_reduction a hL b ha φ hφ]
  exact (IntegralMatrices.reduction_surjective (IsFractionRing.injective O K)).comp
    (L.latticeMatrixEquiv a hL).surjective

end LatticeChain
end Langlands.BushnellKutzko
