import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.SimpleStratumGroups
import Langlands.Group.GL.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Topology of lattice-chain unit groups in standard coordinates -/

open ValuativeRel Topology

noncomputable section

namespace Langlands.BushnellKutzko

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ

local instance endTopology : TopologicalSpace A := moduleTopology F A

section Coordinates

variable [IsTopologicalRing F]

private local instance matrixModuleTopology : IsModuleTopology F (Matrix (Fin n) (Fin n) F) :=
  inferInstanceAs (IsModuleTopology F (Fin n → Fin n → F))

private local instance endContinuousAdd : ContinuousAdd A :=
  IsModuleTopology.toContinuousAdd F A

private def matrixEndContinuousMulEquiv : Matrix (Fin n) (Fin n) F ≃ₜ* A where
  toMulEquiv := Matrix.toLinAlgEquiv'.toMulEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    Matrix.toLinAlgEquiv'.toLinearEquiv.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    Matrix.toLinAlgEquiv'.symm.toLinearEquiv.toLinearMap

/-- Mathlib's `Matrix.GeneralLinearGroup.toLin` with its continuity in both directions.
The endomorphism algebra has the finite-dimensional module topology, and its unit group has the
usual topology on units. -/
def generalLinearToLinContinuous : GeneralLinear n F ≃ₜ* Aut :=
  Units.mapContinuousMulEquiv matrixEndContinuousMulEquiv

@[simp] theorem generalLinearToLinContinuous_toMulEquiv :
    (generalLinearToLinContinuous (F := F) (n := n)).toMulEquiv =
      Matrix.GeneralLinearGroup.toLin := rfl

end Coordinates

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

private local instance endTopologicalRing : IsTopologicalRing A :=
  IsModuleTopology.isTopologicalRing F A

private local instance endT1 : T1Space A :=
  matrixEndContinuousMulEquiv.symm.toHomeomorph.isEmbedding.t1Space

private theorem isLattice_endFiltration (L : LatticeChain 𝒪[F] F (Fin n → F)) (m : ℤ) :
    (L.endFiltration m).IsLattice F := by
  refine ⟨L.fg_endFiltration m, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨k, hk⟩ := L.exists_uniformizer_pow_mem_endFiltration hϖ x m
  have hne : (ϖ : F) ^ k ≠ 0 := pow_ne_zero _ (fun h => hϖ.ne_zero (Subtype.ext h))
  have hx := Submodule.subset_span (R := F) (s := (L.endFiltration m : Set A)) hk
  simpa only [inv_smul_smul₀ hne] using
    (Submodule.span F (L.endFiltration m : Set A)).smul_mem ((ϖ : F) ^ k)⁻¹ hx

private theorem isCompact_isOpen_of_isLattice (P : Submodule 𝒪[F] A) [P.IsLattice F] :
    IsCompact (P : Set A) ∧ IsOpen (P : Set A) := by
  classical
  let b := Module.finBasis 𝒪[F] P
  let c := b.extendOfIsLattice F
  let e := c.equivFun
  let h : A ≃ₜ _ :=
    { toEquiv := e.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  have hrange : Set.range c = P.subtype '' Set.range b := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => b.extendOfIsLattice_apply F i)
  have hspan : Submodule.span 𝒪[F] (Set.range c) = P := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hintegers : Set.range (algebraMap 𝒪[F] F) = (𝒪[F] : Set F) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hP : (P : Set A) = h ⁻¹' Set.pi Set.univ (fun _ => (𝒪[F] : Set F)) := by
    ext x
    rw [Set.mem_preimage, Set.mem_pi]
    simp only [Set.mem_univ, forall_true_left, SetLike.mem_coe]
    change x ∈ P ↔ ∀ i, c.equivFun x i ∈ (𝒪[F] : Set F)
    simp only [Module.Basis.equivFun_apply]
    have hmem := Iff.of_eq (congrArg (fun M : Submodule 𝒪[F] A => x ∈ M) hspan)
    exact hmem.symm.trans (by simpa only [hintegers] using c.mem_span_iff_repr_mem 𝒪[F] x)
  rw [hP, h.isCompact_preimage, h.isOpen_preimage]
  exact ⟨isCompact_univ_pi (fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F 1),
    isOpen_set_pi Set.finite_univ (fun _ _ => Valuation.isOpen_integer (v := valuation F))⟩

/-- The lattice-chain filtration subgroups are open in the topology of the endomorphism group. -/
theorem isOpen_unitFiltration (L : LatticeChain 𝒪[F] F (Fin n → F)) (m : ℕ) :
    IsOpen (L.unitFiltration m : Set Aut) := by
  have := isLattice_endFiltration L 0
  have := isLattice_endFiltration L (m : ℤ)
  have horder : IsOpen (L.order : Set A) := (isCompact_isOpen_of_isLattice (L.endFiltration 0)).2
  have hstep := (isCompact_isOpen_of_isLattice (L.endFiltration m)).2
  exact (horder.preimage Units.continuous_val).inter
    ((horder.preimage (Units.continuous_val.comp continuous_inv)).inter
      (hstep.preimage (Units.continuous_val.sub continuous_const)))

/-- The unit group of a lattice-chain order is compact. -/
theorem isCompact_unitFiltration_zero (L : LatticeChain 𝒪[F] F (Fin n → F)) :
    IsCompact (L.unitFiltration 0 : Set Aut) := by
  have := isLattice_endFiltration L 0
  have hc : IsCompact (L.order.toSubmonoid : Set A) :=
    (isCompact_isOpen_of_isLattice (L.endFiltration 0)).1
  convert Submonoid.units_isCompact hc using 1
  ext g
  exact L.mem_unitFiltration_zero

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_endFiltration_le_simpleJLattice (L : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℤ) (β : A) (tail : List A) :
    ∃ t : ℤ, L.endFiltration t ≤ simpleJLattice L m β tail := by
  induction tail generalizing β with
  | nil => exact ⟨simpleJCutoff m, le_sup_right⟩
  | cons γ tail ih =>
    obtain ⟨t, ht⟩ := ih γ
    let s := simpleJCutoff (finiteCriticalDepth L m β)
    refine ⟨max t s, ?_⟩
    exact le_trans (le_inf ((L.endFiltration_antitone (le_max_left t s)).trans ht)
      (L.endFiltration_antitone (le_max_right t s))) le_sup_right

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem one_mem_simpleJLattice (L : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℤ) (β : A) (tail : List A) : (1 : A) ∈ simpleJLattice L m β tail := by
  have hone : (1 : A) ∈ centralizerLattice L β 0 := by
    refine ⟨show (1 : A) ∈ L.order from one_mem _, ?_⟩
    simp [adjointMap]
  cases tail <;> exact Submodule.mem_sup_left hone

/-- Each simple-stratum subgroup `J^i` is open and compact. -/
theorem isCompact_isOpen_simpleJGroup (L : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℤ) (β : A) (tail : List A) (i : ℕ) :
    IsCompact (simpleJGroup L m β tail i : Set Aut) ∧
      IsOpen (simpleJGroup L m β tail i : Set Aut) := by
  obtain ⟨t, ht⟩ := exists_endFiltration_le_simpleJLattice L m β tail
  let k := max i t.toNat
  have hk : t ≤ (k : ℤ) := by
    dsimp [k]
    omega
  have hopen : IsOpen (simpleJGroup L m β tail i : Set Aut) := by
    refine Subgroup.isOpen_mono (H₁ := L.unitFiltration k) ?_ (isOpen_unitFiltration L k)
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨L.unitFiltration_antitone (le_max_left i t.toNat) hg, ?_⟩
    have hsub := ht (L.endFiltration_antitone hk hg.2.2)
    simpa only [sub_add_cancel] using add_mem hsub (one_mem_simpleJLattice L m β tail)
  exact ⟨(isCompact_unitFiltration_zero L).of_isClosed_subset
    ((simpleJGroup L m β tail i).isClosed_of_isOpen hopen)
    ((simpleJGroup_le_unitFiltration L m β tail i).trans (L.unitFiltration_antitone (Nat.zero_le i))),
    hopen⟩

/-- The depth-`i` simple-stratum group as an open subgroup for restriction of representations. -/
def simpleJOpenSubgroup (L : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℤ) (β : A) (tail : List A) (i : ℕ) : OpenSubgroup Aut :=
  ⟨simpleJGroup L m β tail i, (isCompact_isOpen_simpleJGroup L m β tail i).2⟩

/-- The simple-stratum subgroup `J` is open and compact. -/
theorem isCompact_isOpen_simpleJ (L : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℤ) (β : A) (tail : List A) :
    IsCompact (simpleJ L m β tail : Set Aut) ∧ IsOpen (simpleJ L m β tail : Set Aut) :=
  isCompact_isOpen_simpleJGroup L m β tail 0

end Langlands.BushnellKutzko
