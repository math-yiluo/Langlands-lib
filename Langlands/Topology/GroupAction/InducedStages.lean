import Langlands.Topology.GroupAction.InducedSpace
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Actions

/-! # Induction in stages for actual topological induced spaces -/

noncomputable section

universe u v

namespace Langlands.TopologicalInduction

open Topology

variable {G : Type u} [Group G] (H J : Subgroup G)
  (X : Type v) [MulAction H X]

/-- Forget the intermediate subgroup layer in the intersection subgroup. -/
def stagesSubgroupHom : H.subgroupOf J →* H where
  toFun h := ⟨(h.1 : G), h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original action restricted to `H` as a subgroup of `J`.
This definition is selected locally, rather than installed as a global instance. -/
abbrev stagesAction : MulAction (H.subgroupOf J) X :=
  MulAction.compHom X (stagesSubgroupHom H J)

attribute [local instance] stagesAction

/-- The actual iterated balanced quotient, with the explicit restricted action. -/
abbrev StagedSpace := Space J (Space (H.subgroupOf J) X)

variable {H J X}

private theorem stages_unit_equivariant (h : H.subgroupOf J) (x : X) :
    unit H (h • x) = (h : J) • unit H x :=
  unit_subgroup_smul (stagesSubgroupHom H J h) x

/-- Extend the original unit across the inner induction. -/
def stagesInner : Space (H.subgroupOf J) X → Space H X :=
  lift (unit H) stages_unit_equivariant

@[simp]
theorem stagesInner_mk (j : J) (x : X) :
    stagesInner (mk (H.subgroupOf J) j x) = mk H (j : G) x := by
  simp [stagesInner, Subgroup.smul_def]

theorem stagesInner_smul (j : J) (z : Space (H.subgroupOf J) X) :
    stagesInner (j • z) = (j : G) • stagesInner z :=
  lift_smul (unit H) stages_unit_equivariant j z

/-- Flatten the two quotient representatives by multiplication. -/
def stagesFlatten : StagedSpace H J X → Space H X :=
  lift stagesInner stagesInner_smul

@[simp]
theorem stagesFlatten_mk (g : G) (j : J) (x : X) :
    stagesFlatten (mk J g (mk (H.subgroupOf J) j x)) =
      mk H (g * (j : G)) x := by
  simp [stagesFlatten]

theorem stagesFlatten_smul (g : G) (z : StagedSpace H J X) :
    stagesFlatten (g • z) = g • stagesFlatten z :=
  lift_smul stagesInner stagesInner_smul g z

variable (hHJ : H ≤ J)

private theorem stages_double_unit_equivariant (hHJ : H ≤ J) (h : H) (x : X) :
    unit J (unit (H.subgroupOf J) (h • x)) =
      (h : G) • unit J (unit (H.subgroupOf J) x) := by
  let k : H.subgroupOf J := ⟨⟨(h : G), hHJ h.2⟩, h.2⟩
  change unit J (unit (H.subgroupOf J) (k • x)) = _
  rw [unit_subgroup_smul k, unit_subgroup_smul]

/-- Insert an identity representative in the inner quotient. -/
def stagesInsert : Space H X → StagedSpace H J X :=
  lift (fun x => unit J (unit (H.subgroupOf J) x))
    (stages_double_unit_equivariant hHJ)

@[simp]
theorem stagesInsert_mk (g : G) (x : X) :
    stagesInsert hHJ (mk H g x) =
      mk J g (mk (H.subgroupOf J) 1 x) := by
  simp [stagesInsert, unit]

theorem stagesInsert_smul (g : G) (z : Space H X) :
    stagesInsert hHJ (g • z) = g • stagesInsert hHJ z :=
  lift_smul _ (stages_double_unit_equivariant hHJ) g z

theorem stagesFlatten_insert (z : Space H X) :
    stagesFlatten (stagesInsert hHJ z) = z := by
  induction z using Quotient.inductionOn with
  | h p =>
    change stagesFlatten (stagesInsert hHJ (mk H p.1 p.2)) = mk H p.1 p.2
    simp

theorem stagesInsert_flatten (z : StagedSpace H J X) :
    stagesInsert hHJ (stagesFlatten z) = z := by
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨g, y⟩
    induction y using Quotient.inductionOn with
    | h q =>
      rcases q with ⟨j, x⟩
      change stagesInsert hHJ
        (stagesFlatten (mk J g (mk (H.subgroupOf J) j x))) =
          mk J g (mk (H.subgroupOf J) j x)
      rw [stagesFlatten_mk, stagesInsert_mk]
      simpa [unit] using (mk_balance j g (unit (H.subgroupOf J) x))

/-- The canonical equivalence of the actual balanced quotients. -/
def stagesEquiv : StagedSpace H J X ≃ Space H X where
  toFun := stagesFlatten
  invFun := stagesInsert hHJ
  left_inv := stagesInsert_flatten hHJ
  right_inv := stagesFlatten_insert hHJ

@[simp]
theorem stagesEquiv_mk (g : G) (j : J) (x : X) :
    stagesEquiv hHJ (mk J g (mk (H.subgroupOf J) j x)) =
      mk H (g * (j : G)) x :=
  stagesFlatten_mk g j x

@[simp]
theorem stagesEquiv_double_unit (x : X) :
    stagesEquiv hHJ (unit J (unit (H.subgroupOf J) x)) = unit H x := by
  simp [stagesEquiv, unit]

theorem stagesEquiv_smul (g : G) (z : StagedSpace H J X) :
    stagesEquiv hHJ (g • z) = g • stagesEquiv hHJ z :=
  stagesFlatten_smul g z

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [ContinuousSMul H X]

omit [IsTopologicalGroup G] in
/-- Continuity of the explicitly selected action, on the original topology of `X`. -/
theorem continuousSMul_stagesAction :
    ContinuousSMul (H.subgroupOf J) X :=
  MulAction.continuousSMul_compHom
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun h => h.2))

attribute [local instance] continuousSMul_stagesAction

theorem continuous_stagesInner :
    Continuous (stagesInner : Space (H.subgroupOf J) X → Space H X) :=
  continuous_lift (unit H) stages_unit_equivariant continuous_unit

theorem continuous_stagesFlatten :
    Continuous (stagesFlatten : StagedSpace H J X → Space H X) :=
  continuous_lift stagesInner stagesInner_smul continuous_stagesInner

theorem continuous_stagesInsert :
    Continuous (stagesInsert hHJ : Space H X → StagedSpace H J X) :=
  continuous_lift _ (stages_double_unit_equivariant hHJ)
    (continuous_unit.comp continuous_unit)

/-- Induction in stages as a homeomorphism of actual quotient topologies. -/
def stagesHomeomorph : StagedSpace H J X ≃ₜ Space H X where
  toEquiv := stagesEquiv hHJ
  continuous_toFun := continuous_stagesFlatten
  continuous_invFun := continuous_stagesInsert hHJ

@[simp]
theorem stagesHomeomorph_mk (g : G) (j : J) (x : X) :
    stagesHomeomorph hHJ (mk J g (mk (H.subgroupOf J) j x)) =
      mk H (g * (j : G)) x :=
  stagesFlatten_mk g j x

@[simp]
theorem stagesHomeomorph_symm_mk (g : G) (x : X) :
    (stagesHomeomorph hHJ).symm (mk H g x) =
      mk J g (mk (H.subgroupOf J) 1 x) :=
  stagesInsert_mk hHJ g x

@[simp]
theorem stagesHomeomorph_double_unit (x : X) :
    stagesHomeomorph hHJ (unit J (unit (H.subgroupOf J) x)) = unit H x :=
  stagesEquiv_double_unit hHJ x

theorem stagesHomeomorph_smul (g : G) (z : StagedSpace H J X) :
    stagesHomeomorph hHJ (g • z) = g • stagesHomeomorph hHJ z :=
  stagesFlatten_smul g z

end Topology

end Langlands.TopologicalInduction
