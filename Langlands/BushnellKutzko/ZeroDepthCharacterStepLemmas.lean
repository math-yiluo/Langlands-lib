import Langlands.BushnellKutzko.SimpleTypeTopology
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.BetaExtensionTwist.DomainProduct
import Langlands.BushnellKutzko.SplitObstructionLattice
import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.StratumExistence

/-! # The groups `J(β, 𝔄) ⊇ J^1(β, 𝔄)` of a simple stratum of level zero

Group-theoretic and topological facts about the groups `J = J(β, 𝔄)` and `J^1 = J^1(β, 𝔄)` of
a simple stratum `[𝔄, n, 0, β]`, used in BK93 (8.1.5), printed pp. 268–269.
-/

open ValuativeRel Topology

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uV

section Groups

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V

/-- `U^m(𝔅_β) = U^m(𝔄) ∩ B_β^×` lies in `J^m(β, 𝔄)`. -/
theorem relativeUnitFiltration_le_simpleJGroup (L : LatticeChain O F V) (n : ℤ) (β : A)
    (tail : List A) (m : ℕ) : relativeUnitFiltration L β m ≤ simpleJGroup L n β tail m := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.2, ?_⟩
  have hc : (g : A) ∈ centralizerLattice L β 0 := by
    refine ⟨L.mem_order_iff_mem_endFiltration.1 hg.2.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h : β * (g : A) = (g : A) * β := hg.1
    simp [adjointMap, h]
  cases tail <;> exact Submodule.mem_sup_left hc

/-- Some step `𝔓^t` of the filtration of `A` lies in `𝔍(β, 𝔄)`. -/
theorem exists_endFiltration_le_simpleJLattice' (L : LatticeChain O F V) (n : ℤ) (β : A)
    (tail : List A) : ∃ t : ℤ, L.endFiltration t ≤ simpleJLattice L n β tail := by
  induction tail generalizing β with
  | nil => exact ⟨simpleJCutoff n, le_sup_right⟩
  | cons γ tail ih =>
    obtain ⟨t, ht⟩ := ih γ
    let s := simpleJCutoff (finiteCriticalDepth L n β)
    refine ⟨max t s, ?_⟩
    exact le_trans (le_inf ((L.endFiltration_antitone (le_max_left t s)).trans ht)
      (L.endFiltration_antitone (le_max_right t s))) le_sup_right

/-- The identity lies in `𝔍(β, 𝔄)`. -/
theorem one_mem_simpleJLattice' (L : LatticeChain O F V) (n : ℤ) (β : A) (tail : List A) :
    (1 : A) ∈ simpleJLattice L n β tail := by
  have hone : (1 : A) ∈ centralizerLattice L β 0 := by
    refine ⟨show (1 : A) ∈ L.order from one_mem _, ?_⟩
    simp [adjointMap]
  cases tail <;> exact Submodule.mem_sup_left hone

/-- Some `U^k(𝔄)` lies in `J^m(β, 𝔄)`. -/
theorem exists_unitFiltration_le_simpleJGroup (L : LatticeChain O F V) (n : ℤ) (β : A)
    (tail : List A) (m : ℕ) : ∃ k : ℕ, L.unitFiltration k ≤ simpleJGroup L n β tail m := by
  obtain ⟨t, ht⟩ := exists_endFiltration_le_simpleJLattice' L n β tail
  refine ⟨max m t.toNat, fun g hg => Subgroup.subset_closure
    ⟨L.unitFiltration_antitone (le_max_left _ _) hg, ?_⟩⟩
  have hsub := ht (L.endFiltration_antitone
    (show t ≤ ((max m t.toNat : ℕ) : ℤ) by omega) hg.2.2)
  simpa only [sub_add_cancel] using add_mem hsub (one_mem_simpleJLattice' L n β tail)

end Groups

section Simple

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "G" => (Module.End F V)ˣ

/-- For a simple stratum `[𝔄, n, 0, β]`, `J^1(β, 𝔄)` is normal in `J(β, 𝔄)`. -/
theorem simpleJGroup_one_subgroupOf_normal (S : Stratum 𝒪[F] F V) (hr : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) :
    ((simpleJGroup S.chain S.n S.b q.tail 1).subgroupOf
      (simpleJ S.chain S.n S.b q.tail)).Normal := by
  have hcarrier : (simpleJ S.chain S.n S.b q.tail : Set G) =
      simpleJCarrier S.chain S.n S.b q.tail 0 :=
    ((simpleStratumGroupProperties F V S hr hs q).1 0).2
  have hJ1 := simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail
  constructor
  intro h hh j
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  have hmem : ((j * h * j⁻¹ : simpleJ S.chain S.n S.b q.tail) : G) ∈
      simpleJCarrier S.chain S.n S.b q.tail 0 := by
    rw [← hcarrier]
    exact (j * h * j⁻¹).2
  apply Subgroup.subset_closure
  refine ⟨?_, hmem.2⟩
  have hj : ((j⁻¹ : simpleJ S.chain S.n S.b q.tail) : G) ∈ S.chain.unitFiltration 0 :=
    simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail 0 (j⁻¹).2
  have := S.chain.inv_mul_mul_mem_unitFiltration hj
    (simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail 1 hh)
  simpa [mul_assoc] using this

/-- For a simple stratum `[𝔄, n, 0, β]`, `J(β, 𝔄) = U(𝔅_β) J^1(β, 𝔄)`. -/
theorem exists_relativeUnit_mul_simpleJGroup_one (S : Stratum 𝒪[F] F V) (hr : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) {d : G}
    (hd : d ∈ simpleJ S.chain S.n S.b q.tail) :
    ∃ u ∈ relativeUnitFiltration S.chain S.b 0, ∃ k ∈ simpleJGroup S.chain S.n S.b q.tail 1,
      u * k = d := by
  have hcarrier : (simpleJ S.chain S.n S.b q.tail : Set G) =
      simpleJCarrier S.chain S.n S.b q.tail 0 :=
    ((simpleStratumGroupProperties F V S hr hs q).1 0).2
  have hd' : d ∈ intertwiningDomain (simpleJ S.chain S.n S.b q.tail)
      (simpleJ S.chain S.n S.b q.tail) 1 :=
    mem_intertwiningDomain.mpr ⟨by simpa using hd, hd⟩
  obtain ⟨u, k, huk⟩ := simpleJ_intertwiningDomain_product S hr hs q hcarrier 1
    (centralizerUnitGroup S.b).one_mem ⟨d, hd'⟩
  exact ⟨u, u.2.2, k, k.2.2, huk⟩

end Simple

section Topology

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ

private local instance zeroDepthEndTopology : TopologicalSpace A := moduleTopology F A

private local instance zeroDepthEndTopologicalRing : IsTopologicalRing A :=
  IsModuleTopology.isTopologicalRing F A

/-- Every neighbourhood of the identity of `Aut_F(F^N)` contains some `U^m(𝔄)`. -/
theorem exists_unitFiltration_subset_nhds_aut (L : LatticeChain 𝒪[F] F (Fin n → F))
    {K : Set Aut} (hK : K ∈ 𝓝 (1 : Aut)) :
    ∃ m : ℕ, (L.unitFiltration m : Set Aut) ⊆ K := by
  let U : ℕ → Set Aut := fun m => (L.unitFiltration m : Set Aut)
  have hdir : Directed (· ⊇ ·) U := fun i j =>
    ⟨max i j, L.unitFiltration_antitone (le_max_left i j),
      L.unitFiltration_antitone (le_max_right i j)⟩
  have hclosed : ∀ m, IsClosed (U m) := fun m =>
    (L.unitFiltration m).isClosed_of_isOpen (isOpen_unitFiltration L m)
  have hcpt : ∀ m, IsCompact (U m) := fun m =>
    (isCompact_unitFiltration_zero L).of_isClosed_subset (hclosed m)
      (L.unitFiltration_antitone (Nat.zero_le m))
  have hinter : (⋂ m, U m) = {1} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    refine ⟨fun hg => ?_, fun hg m => hg ▸ (L.unitFiltration m).one_mem⟩
    have h0 : (g : A) - 1 = 0 :=
      SplitObstruction.eq_zero_of_forall_ge_mem L (k₀ := 0) fun k => by
        simpa using (hg k).2.2
    exact Units.ext (sub_eq_zero.mp h0)
  exact exists_subset_nhds_of_isCompact' hdir hcpt hclosed
    (by rw [hinter, nhdsSet_singleton]; exact hK)

/-- Every neighbourhood of the identity of `GL_N(F)` contains the image of some `U^m(𝔄)`. -/
theorem exists_unitFiltration_subset_nhds (L : LatticeChain 𝒪[F] F (Fin n → F))
    {K : Set (GeneralLinear n F)} (hK : K ∈ 𝓝 (1 : GeneralLinear n F)) :
    ∃ m : ℕ, ∀ g ∈ L.unitFiltration m, Matrix.GeneralLinearGroup.toLin.symm g ∈ K := by
  let e := generalLinearToLinContinuous (F := F) (n := n)
  have hK' : e.symm ⁻¹' K ∈ 𝓝 (1 : Aut) := by
    apply e.symm.continuous.continuousAt.preimage_mem_nhds
    simpa using hK
  obtain ⟨m, hm⟩ := exists_unitFiltration_subset_nhds_aut L hK'
  exact ⟨m, fun g hg => hm hg⟩

/-- For any two lattice chains `𝓛, 𝓜` in `F^N` and any `m`, some `U^k(𝓛)` lies in
`U^m(𝓜)`. -/
theorem exists_unitFiltration_le_unitFiltration (L M : LatticeChain 𝒪[F] F (Fin n → F))
    (m : ℕ) : ∃ k : ℕ, L.unitFiltration k ≤ M.unitFiltration m := by
  obtain ⟨k, hk⟩ := exists_unitFiltration_subset_nhds_aut L
    ((isOpen_unitFiltration M m).mem_nhds (M.unitFiltration m).one_mem)
  exact ⟨k, fun g hg => hk hg⟩

/-- `U^m(𝔄) ∩ J^j(β, 𝔄)` has finite index in `J^j(β, 𝔄)`. -/
theorem finiteIndex_unitFiltration_subgroupOf_simpleJGroup
    (L M : LatticeChain 𝒪[F] F (Fin n → F)) (k : ℤ) (β : A) (tail : List A) (j m : ℕ) :
    ((M.unitFiltration m).subgroupOf (simpleJGroup L k β tail j)).FiniteIndex := by
  obtain ⟨t, ht⟩ := exists_unitFiltration_le_simpleJGroup L k β tail j
  have hopen : IsOpen (simpleJGroup L k β tail j : Set Aut) :=
    Subgroup.isOpen_mono ht (isOpen_unitFiltration L t)
  have hcpt : IsCompact (simpleJGroup L k β tail j : Set Aut) :=
    (isCompact_unitFiltration_zero L).of_isClosed_subset
      ((simpleJGroup L k β tail j).isClosed_of_isOpen hopen)
      (simpleJGroup_le_unitFiltration L k β tail j |>.trans
        (L.unitFiltration_antitone (Nat.zero_le j)))
  have : CompactSpace (simpleJGroup L k β tail j) := isCompact_iff_compactSpace.mp hcpt
  have hK : IsOpen (((M.unitFiltration m).subgroupOf (simpleJGroup L k β tail j) :
      Subgroup (simpleJGroup L k β tail j)) : Set (simpleJGroup L k β tail j)) :=
    (isOpen_unitFiltration M m).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hK
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end Langlands.BushnellKutzko
