import Langlands.LocalField.Definitions
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Units

/-!
# Profinite completion using the open finite quotients

The closure of the diagonal image in the product of all open finite quotients
is a concrete profinite group. The original topology is used on the source.
No local reciprocity homomorphism or isomorphism is assumed.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

namespace ContinuousProfinite

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The existing finite-index normal subgroups that are open in the given topology. -/
abbrev OpenFiniteQuotient :=
  {N : FiniteIndexNormalSubgroup G // IsOpen (N.toSubgroup : Set G)}

namespace OpenFiniteQuotient

variable {G} (N : OpenFiniteQuotient G)

/-- The actual group quotient, carrying its quotient topology. -/
abbrev Quotient := G ⧸ N.1.toSubgroup

instance quotientDiscrete : DiscreteTopology N.Quotient :=
  QuotientGroup.discreteTopology N.2

/-- The continuous quotient projection to this finite discrete group. -/
def projection : G →ₜ* N.Quotient where
  toMonoidHom := QuotientGroup.mk' _
  continuous_toFun := QuotientGroup.continuous_mk

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pull back an actual open finite quotient along a continuous homomorphism. -/
def comap (f : H →ₜ* G) : OpenFiniteQuotient H :=
  ⟨N.1.comap f.toMonoidHom, N.2.preimage f.continuous⟩

/-- The induced continuous homomorphism on finite quotients. -/
def quotientMap (f : H →ₜ* G) : (N.comap f).Quotient →ₜ* N.Quotient where
  toMonoidHom := QuotientGroup.map _ _ f.toMonoidHom (fun _ h => h)
  continuous_toFun := continuous_of_discreteTopology

end OpenFiniteQuotient

/-- The product of all actual open finite quotients, with its product topology. -/
abbrev QuotientProduct := ∀ N : OpenFiniteQuotient G, N.Quotient

/-- The diagonal continuous homomorphism into the product of finite quotients. -/
def diagonal : G →ₜ* QuotientProduct G where
  toFun g N := N.projection g
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun N => N.projection.continuous

/-- The closed subgroup generated topologically by the diagonal image.
This is a closure of a subgroup, not a choice of a reciprocity map. -/
def imageClosure : Subgroup (QuotientProduct G) :=
  (diagonal G).toMonoidHom.range.topologicalClosure

/-- A concrete completion for the topology of open finite-index normal subgroups.
Its topology is the subspace topology in the product of quotient topologies. -/
abbrev Completion := imageClosure G

instance completionCompact : CompactSpace (Completion G) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (diagonal G).toMonoidHom.range).isCompact

/-- The completion packaged as an actual profinite group. -/
def profiniteGroup : ProfiniteGrp := ProfiniteGrp.of (Completion G)

/-- The canonical continuous homomorphism from the original topological group.
Injectivity is not asserted for a general group. -/
def eta : G →ₜ* Completion G where
  toFun g := ⟨diagonal G g, Subgroup.le_topologicalClosure _ ⟨g, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (diagonal G).continuous.subtype_mk _

/-- Density is intrinsic to the closure construction. -/
theorem eta_dense : DenseRange (eta G) := by
  rw [DenseRange, Subtype.dense_iff]
  rw [← Set.range_comp]
  change closure (Set.range (diagonal G)) ⊆ closure (Set.range (diagonal G))
  exact Set.Subset.rfl

/-- The canonical continuous coordinate map from the completion to a finite quotient. -/
def projection (N : OpenFiniteQuotient G) : Completion G →ₜ* N.Quotient where
  toFun x := x.1 N
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_apply N).comp continuous_subtype_val

variable {G} {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pullback of quotient coordinates defines a continuous map of the products. -/
def productMap (f : G →ₜ* H) : QuotientProduct G →ₜ* QuotientProduct H where
  toFun x N := N.quotientMap f (x (N.comap f))
  map_one' := by ext N; exact map_one (N.quotientMap f)
  map_mul' x y := by ext N; exact map_mul (N.quotientMap f) _ _
  continuous_toFun := continuous_pi fun N =>
    (N.quotientMap f).continuous.comp (continuous_apply (N.comap f))

private theorem productMap_mem_closure (f : G →ₜ* H) (x : Completion G) :
    productMap f x.1 ∈ imageClosure H := by
  apply closure_mono (s := (productMap f) '' Set.range (diagonal G)) ?_
    (image_closure_subset_closure_image (productMap f).continuous ⟨x.1, x.2, rfl⟩)
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨f g, rfl⟩

/-- The actual map of completions induced by a continuous group homomorphism. -/
def map (f : G →ₜ* H) : Completion G →ₜ* Completion H where
  toFun x := ⟨productMap f x.1, productMap_mem_closure f x⟩
  map_one' := by apply Subtype.ext; exact map_one (productMap f)
  map_mul' x y := by apply Subtype.ext; exact map_mul (productMap f) x.1 y.1
  continuous_toFun :=
    ((productMap f).continuous.comp continuous_subtype_val).subtype_mk _

end ContinuousProfinite

namespace LocalMultiplicative

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  (T : F.TopologicalData)

/-- The profinite completion of the actual multiplicative topological group,
using precisely its open finite-index subgroups. It is not the group `Fˣ`. -/
def profiniteCompletion : ProfiniteGrp := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact ContinuousProfinite.profiniteGroup F.Carrierˣ

/-- The canonical continuous map from `Fˣ` into that profinite completion. -/
def completionMap :
    letI := T.topology
    F.Carrierˣ →ₜ* profiniteCompletion T := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact ContinuousProfinite.eta F.Carrierˣ

/-- The local multiplicative completion map has dense image by construction. -/
theorem completionMap_dense :
    letI := T.topology
    DenseRange (completionMap T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ContinuousProfinite.eta_dense F.Carrierˣ

end LocalMultiplicative

end Langlands.LocalClassField
