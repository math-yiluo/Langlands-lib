import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Generic points of all fibres of a scheme morphism -/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Images in the total scheme of the generic points of all fibre components. -/
def fibreGenericPoints (p : X ⟶ S) : Set X :=
  ⋃ s : S, (p.fiberι s) '' genericPoints (p.fiber s)

/-- A subset contains a same-fibre generization of every point. -/
def FibreGenerizationDense (p : X ⟶ S) (U : Set X) : Prop :=
  ∀ x : X, ∃ y : X, y ∈ U ∧ p y = p x ∧ y ⤳ x

/-- The generic points of the fibres specialize, within their fibres, to all points. -/
theorem exists_fibreGenericPoint_specializes (p : X ⟶ S) (x : X) :
    ∃ y ∈ fibreGenericPoints p, p y = p x ∧ y ⤳ x := by
  let z := p.asFiber x
  let C : irreducibleComponents (p.fiber (p x)) :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  let g := genericPoints.ofComponent C
  refine ⟨p.fiberι (p x) g.1, Set.mem_iUnion.mpr ⟨p x, ⟨g.1, g.2, rfl⟩⟩,
    (p.fiberHomeo (p x) g.1).2, ?_⟩
  have hgz : g.1 ⤳ z :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  simpa only [z, Scheme.Hom.fiberι_asFiber] using hgz.map (p.fiberι (p x)).continuous

/-- Containing all fibre-component generic points is equivalent to same-fibre
generization density. No finiteness or nonempty-fibre assumption is needed. -/
theorem fibreGenericPoints_subset_iff (p : X ⟶ S) (U : Set X) :
    fibreGenericPoints p ⊆ U ↔ FibreGenerizationDense p U := by
  constructor
  · intro h x
    obtain ⟨y, hy, hpy, hyx⟩ := exists_fibreGenericPoint_specializes p x
    exact ⟨y, h hy, hpy, hyx⟩
  · intro h x hx
    obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, hpy, hyx⟩ := h (p.fiberι s z)
    have hps : p (p.fiberι s z) = s := (p.fiberHomeo s z).2
    let w := (p.fiberHomeo s).symm ⟨y, hpy.trans hps⟩
    have hw : p.fiberι s w = y := p.fiberι_fiberHomeo_symm s _
    have hwz : w ⤳ z := (p.fiberι s).isEmbedding.specializes_iff.mp (hw ▸ hyx)
    have hEq : w = z := GenericPointAvoidance.mem_genericPoints_iff.mp hz _ hwz
    simpa only [← hw, hEq] using hy

/-- Over a finite base, a quasi-compact morphism locally of finite type has
only finitely many images of fibre-component generic points. -/
theorem finite_fibreGenericPoints (p : X ⟶ S) [Finite S] [LocallyOfFiniteType p]
    [QuasiCompact p] : (fibreGenericPoints p).Finite := by
  apply Set.finite_iUnion
  intro s
  have : LocallyOfFiniteType (p.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (Limits.pullback.snd p (S.fromSpecResidueField s))
    infer_instance
  have : IsLocallyNoetherian (p.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField s)
  have : IsNoetherian (p.fiber s) := {}
  exact (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image _

end Langlands.AlgebraicGeometry
