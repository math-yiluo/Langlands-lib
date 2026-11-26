import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.PositiveZeroSplitType
import Langlands.BushnellKutzko.UnequalPositiveSplitType

/-! # Split types in the matrix general linear group -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uρ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "G" => GeneralLinear n F
local notation "CoordSpace" => (Fin n → F)
local notation "A" => Module.End F CoordSpace
local notation "Aut" => (Module.End F CoordSpace)ˣ

/-- Split types in `GL_n(F)` with positive second level, transported along `toLin`. -/
def IsGLPositiveLevelSplitType {K : Subgroup (GeneralLinear n F)}
    (ψF : AddChar F ℂ) (ρ : SmoothRep.{0, uF, uρ} ℂ K) : Prop :=
  let σ := glRepresentationToAut (F := F) (n := n) (J := K) ρ
  (∃ x, IsDiagonalPositiveSplitType (V := CoordSpace) ψF x σ) ∨
    ∃ x y, IsUnequalPositiveSplitType (V := CoordSpace) ψF x y σ

/-- Split types in `GL_n(F)` of level `(x,0)`, including `x = 0`, transported along `toLin`. -/
def IsGLZeroSecondLevelSplitType {K : Subgroup (GeneralLinear n F)}
    (ψF : AddChar F ℂ) (ρ : SmoothRep.{0, uF, uρ} ℂ K) : Prop :=
  let σ := glRepresentationToAut (F := F) (n := n) (J := K) ρ
  IsLevelZeroSplitType (V := CoordSpace) σ ∨
    ∃ x, IsPositiveZeroSplitType (V := CoordSpace) ψF x σ

/-- **BK93 §8.1.** A split type in `GL_n(F)` is a pair of any of the four kinds
after transport along `toLin`. -/
def IsGLSplitType {K : Subgroup (GeneralLinear n F)}
    (ψF : AddChar F ℂ) (ρ : SmoothRep.{0, uF, uρ} ℂ K) : Prop :=
  IsGLPositiveLevelSplitType (n := n) (K := K) ψF ρ ∨
    IsGLZeroSecondLevelSplitType (n := n) (K := K) ψF ρ

private local instance splitTypeEndTopology : TopologicalSpace A := moduleTopology F A
private local instance splitTypeEndTopologicalRing : IsTopologicalRing A :=
  IsModuleTopology.isTopologicalRing F A

private theorem isCompact_isOpen_of_between_filtrations (L : LatticeChain 𝒪[F] F CoordSpace) (k : ℕ)
    (U : Subgroup Aut) (h₁ : L.unitFiltration k ≤ U) (h₂ : U ≤ L.unitFiltration 0) :
    IsCompact (U : Set Aut) ∧ IsOpen (U : Set Aut) := by
  have hopen := Subgroup.isOpen_mono h₁ (isOpen_unitFiltration L k)
  exact ⟨(isCompact_unitFiltration_zero L).of_isClosed_subset (U.isClosed_of_isOpen hopen) h₂, hopen⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_endFiltration_le_simpleHLattice (L : LatticeChain 𝒪[F] F CoordSpace) (d : ℤ)
    (β : A) (tail : List A) :
    ∃ t : ℤ, L.endFiltration t ≤ simpleHLattice L d β tail := by
  induction tail generalizing β with
  | nil => exact ⟨simpleHCutoff d, le_sup_right⟩
  | cons γ tail ih =>
    obtain ⟨t, ht⟩ := ih γ
    let s := simpleHCutoff (finiteCriticalDepth L d β)
    exact ⟨max t s, (le_inf ((L.endFiltration_antitone (le_max_left t s)).trans ht)
      (L.endFiltration_antitone (le_max_right t s))).trans le_sup_right⟩

private theorem isCompact_isOpen_simpleH (L : LatticeChain 𝒪[F] F CoordSpace) (d : ℤ)
    (β : A) (tail : List A) (m : ℕ) :
    IsCompact (simpleHGroup L d β tail m : Set Aut) ∧
      IsOpen (simpleHGroup L d β tail m : Set Aut) := by
  obtain ⟨t, ht⟩ := exists_endFiltration_le_simpleHLattice L d β tail
  let k := max m t.toNat
  have hmk : m ≤ k := le_max_left _ _
  have htk : t ≤ (k : ℤ) := by dsimp [k]; omega
  have hcent : (1 : A) ∈ centralizerLattice L β 0 := by
    refine ⟨show (1 : A) ∈ L.order from one_mem _, ?_⟩
    simp [adjointMap]
  have hone : (1 : A) ∈ simpleHLattice L d β tail := by
    cases tail <;> exact Submodule.mem_sup_left hcent
  refine isCompact_isOpen_of_between_filtrations L k _ ?_
    ((simpleHGroup_le_unitFiltration L d β tail m).trans
      (L.unitFiltration_antitone (Nat.zero_le m)))
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨L.unitFiltration_antitone hmk hg, ?_⟩
  simpa only [sub_add_cancel] using add_mem (ht (L.endFiltration_antitone htk hg.2.2)) hone

variable {ψF : AddChar F ℂ} {K : Subgroup (GeneralLinear n F)}
  {ρ : SmoothRep.{0, uF, uρ} ℂ K}

private theorem isCompact_isOpen_image_of_isGLSplitType
    (h : IsGLSplitType (n := n) (K := K) ψF ρ) :
    IsCompact (glSubgroupToAut (F := F) (n := n) K : Set Aut) ∧
      IsOpen (glSubgroupToAut (F := F) (n := n) K : Set Aut) := by
  rcases h with h | h
  · rcases h with ⟨_, ⟨_, S, _, _, _, _, hp⟩⟩ |
      ⟨_, _, ⟨_, S, q, j, _, _, _, _, _, _, _, _, _, _, hp⟩⟩
    · rw [hp.choose]
      exact isCompact_isOpen_of_between_filtrations S.chain S.n.toNat _ le_rfl
        (S.chain.unitFiltration_antitone (Nat.zero_le _))
    · rw [hp.choose]
      exact isCompact_isOpen_simpleH S.chain S.n S.b q.tail (j + 1)
  · rcases h with ⟨L, _, _, _, hp⟩ | ⟨_, h⟩
    · rw [hp.choose]
      exact ⟨isCompact_unitFiltration_zero L, isOpen_unitFiltration L 0⟩
    · obtain ⟨_, _, S, q, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp⟩ := h
      rw [hp.choose]
      exact isCompact_isOpen_simpleJ S.chain S.n S.b q.tail

/-- The subgroup in a split type in matrix coordinates is compact and open. -/
theorem IsGLSplitType.isCompact_isOpen (h : IsGLSplitType (n := n) (K := K) ψF ρ) :
    IsCompact (K : Set G) ∧ IsOpen (K : Set G) := by
  let e := generalLinearToLinContinuous (F := F) (n := n)
  have hK : (K : Set G) = e ⁻¹' (glSubgroupToAut (F := F) (n := n) K : Set Aut) := by
    ext g
    exact (Subgroup.mem_map_iff_mem (Matrix.GeneralLinearGroup.toLin : G ≃* Aut).injective).symm
  obtain ⟨hc, ho⟩ := isCompact_isOpen_image_of_isGLSplitType h
  rw [hK]
  exact ⟨e.toHomeomorph.isCompact_preimage.mpr hc, ho.preimage e.continuous⟩

end Langlands.BushnellKutzko
