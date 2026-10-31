import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # A discrete copy of an operator group -/

universe v w z

namespace Langlands.Topology

/-- A separate type synonym carries the discrete topology independently of
any original topology on the operator group. -/
def DiscreteOperatorGroup (G : Type v) := G

namespace DiscreteOperatorGroup

variable {G : Type v} {H : Type w} {J : Type z}

instance [Group G] : Group (DiscreteOperatorGroup G) :=
  inferInstanceAs (Group G)

instance : TopologicalSpace (DiscreteOperatorGroup G) := ⊥

instance : DiscreteTopology (DiscreteOperatorGroup G) := ⟨rfl⟩

/-- The continuous original-value homomorphism from the discrete group copy. -/
def toOriginal (G : Type v) [Group G] [TopologicalSpace G] :
    DiscreteOperatorGroup G →ₜ* G where
  toFun := id
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem toOriginal_apply [Group G] [TopologicalSpace G]
    (g : DiscreteOperatorGroup G) : toOriginal G g = g := rfl

/-- Every abstract homomorphism induces a continuous map between discrete
copies; no topology on the original groups is needed. -/
def map [Group G] [Group H] (f : G →* H) :
    DiscreteOperatorGroup G →ₜ* DiscreteOperatorGroup H where
  toFun := f
  map_one' := f.map_one
  map_mul' := f.map_mul
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem map_apply [Group G] [Group H] (f : G →* H)
    (g : DiscreteOperatorGroup G) : map f g = f g := rfl

@[simp]
theorem map_id [Group G] :
    map (MonoidHom.id G) = ContinuousMonoidHom.id (DiscreteOperatorGroup G) := by
  ext g
  rfl

@[simp]
theorem map_comp [Group G] [Group H] [Group J] (f : G →* H) (h : H →* J) :
    map (h.comp f) = (map h).comp (map f) := by
  ext g
  rfl

/-- The maps from discrete copies commute with every original continuous
group homomorphism. -/
theorem toOriginal_naturality [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (f : G →ₜ* H) :
    (toOriginal H).comp (map f.toMonoidHom) = f.comp (toOriginal G) := by
  ext g
  rfl

end DiscreteOperatorGroup

end Langlands.Topology
