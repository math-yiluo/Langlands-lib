import Langlands.Topology.GroupAction.InducedSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Clopen
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Coset copies and translated charts of an induced space -/

noncomputable section

universe u v

namespace Langlands.TopologicalInduction

open Topology

variable {G : Type u} [Group G] (H : Subgroup G)
  {X : Type v} [MulAction H X]

/-- The copy of the subgroup space translated by a group element. -/
def chart (g : G) (x : X) : Space H X := mk H g x

/-- The left coset containing the first coordinate of a representative. -/
def component : Space H X → G ⧸ H :=
  Quotient.lift (fun p : Representatives H X => (p.1 : G ⧸ H)) (by
    intro p q e
    obtain ⟨h, rfl⟩ := e
    change ((q.1 * (h : G)⁻¹ : G) : G ⧸ H) = (q.1 : G ⧸ H)
    exact QuotientGroup.mk_mul_of_mem q.1 (H.inv_mem h.property))

@[simp]
theorem component_mk (g : G) (x : X) :
    component H (mk H g x) = (g : G ⧸ H) := rfl

@[simp]
theorem component_chart (g : G) (x : X) :
    component H (chart H g x) = (g : G ⧸ H) := rfl

theorem chart_eq_smul_unit (g : G) (x : X) :
    chart H g x = g • unit H x := (smul_unit g x).symm

theorem chart_injective (g : G) : Function.Injective (chart H g : X → Space H X) := by
  intro x y e
  apply unit_injective (H := H)
  have he := congrArg (fun z : Space H X => g⁻¹ • z) e
  simpa only [chart_eq_smul_unit, inv_smul_smul] using he

/-- Changing a representative within its coset changes the local coordinate by
the original subgroup action. -/
theorem chart_mul_subgroup (g : G) (h : H) (x : X) :
    chart H (g * (h : G)) x = chart H g (h • x) :=
  mk_balance h g x

theorem smul_chart (a g : G) (x : X) :
    a • chart H g x = chart H (a * g) x := rfl

theorem range_chart_eq_fiber (g : G) :
    Set.range (chart H g : X → Space H X) =
      component H ⁻¹' {(g : G ⧸ H)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact component_chart H g x
  · intro hz
    induction z using Quotient.inductionOn with
    | h p =>
      have he : (p.1 : G ⧸ H) = (g : G ⧸ H) := hz
      let h : H := ⟨g⁻¹ * p.1, QuotientGroup.eq.mp he.symm⟩
      refine ⟨h • p.2, ?_⟩
      change mk H g (h • p.2) = mk H p.1 p.2
      simpa [chart, h, mul_assoc] using (mk_balance h g p.2).symm

theorem iUnion_range_chart :
    (⋃ g : G, Set.range (chart H g : X → Space H X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  induction z using Quotient.inductionOn with
  | h p => exact Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩

/-- One copy of the original space for each left coset. -/
abbrev CosetCopies (H : Subgroup G) (X : Type v) := Σ _c : G ⧸ H, X

/-- Send the copy indexed by a coset into the balanced quotient, using the
chosen representative of that coset. -/
def ofCosetCopies (p : CosetCopies H X) : Space H X :=
  chart H p.1.out p.2

@[simp]
theorem component_ofCosetCopies (p : CosetCopies H X) :
    component H (ofCosetCopies H p) = p.1 :=
  QuotientGroup.out_eq' p.1

theorem ofCosetCopies_injective : Function.Injective (ofCosetCopies H (X := X)) := by
  rintro ⟨c, x⟩ ⟨d, y⟩ e
  have hcd : c = d := by
    simpa only [component_ofCosetCopies] using congrArg (component H) e
  cases hcd
  have hxy : x = y := chart_injective H c.out e
  cases hxy
  rfl

theorem ofCosetCopies_surjective : Function.Surjective (ofCosetCopies H (X := X)) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H p.1
    refine ⟨⟨(p.1 : G ⧸ H), h⁻¹ • p.2⟩, ?_⟩
    change mk H (p.1 : G ⧸ H).out (h⁻¹ • p.2) = mk H p.1 p.2
    rw [hh, mk_balance, smul_inv_smul]

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [ContinuousSMul H X]

theorem continuous_chart (g : G) : Continuous (chart H g : X → Space H X) := by
  have he : (chart H g : X → Space H X) = (fun z => g • z) ∘ unit H :=
    funext (chart_eq_smul_unit H g)
  rw [he]
  exact (continuous_const_smul g).comp continuous_unit

omit [IsTopologicalGroup G] [ContinuousSMul H X] in
theorem continuous_component : Continuous (component H : Space H X → G ⧸ H) :=
  (QuotientGroup.continuous_mk.comp continuous_fst).quotient_lift _

theorem isOpenEmbedding_chart (hH : IsOpen (H : Set G)) (g : G) :
    IsOpenEmbedding (chart H g : X → Space H X) := by
  have he : (chart H g : X → Space H X) =
      (Homeomorph.smul g : Space H X ≃ₜ Space H X) ∘ unit H :=
    funext (chart_eq_smul_unit H g)
  rw [he]
  exact (Homeomorph.smul g).isOpenEmbedding.comp (isOpenEmbedding_unit hH)

omit [ContinuousSMul H X] in
theorem isClopen_range_chart (hH : IsOpen (H : Set G)) (g : G) :
    IsClopen (Set.range (chart H g : X → Space H X)) := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  rw [range_chart_eq_fiber]
  exact (isClopen_discrete {(g : G ⧸ H)}).preimage (continuous_component H)

theorem continuous_ofCosetCopies : Continuous (ofCosetCopies H (X := X)) :=
  continuous_sigma fun c => continuous_chart H c.out

theorem isOpenMap_ofCosetCopies (hH : IsOpen (H : Set G)) :
    IsOpenMap (ofCosetCopies H (X := X)) :=
  isOpenMap_sigma.mpr fun c => (isOpenEmbedding_chart H hH c.out).isOpenMap

/-- The balanced quotient is the actual topological coproduct of its coset
copies when the subgroup is open. -/
def cosetCopiesHomeomorph (hH : IsOpen (H : Set G)) :
    CosetCopies H X ≃ₜ Space H X :=
  (Equiv.ofBijective (ofCosetCopies H)
    ⟨ofCosetCopies_injective H, ofCosetCopies_surjective H⟩).toHomeomorphOfContinuousOpen
      (continuous_ofCosetCopies H) (isOpenMap_ofCosetCopies H hH)

@[simp]
theorem cosetCopiesHomeomorph_apply (hH : IsOpen (H : Set G)) (c : G ⧸ H) (x : X) :
    cosetCopiesHomeomorph H hH ⟨c, x⟩ = chart H c.out x := rfl

/-- The action in coset coordinates is exactly the subgroup action determined
by the equation between the chosen representatives. -/
theorem smul_cosetCopiesHomeomorph (hH : IsOpen (H : Set G))
    (a : G) (c d : G ⧸ H) (h : H) (he : a * c.out = d.out * (h : G)) (x : X) :
    a • cosetCopiesHomeomorph H hH ⟨c, x⟩ =
      cosetCopiesHomeomorph H hH ⟨d, h • x⟩ := by
  change mk H (a * c.out) x = mk H d.out (h • x)
  rw [he, mk_balance]

end Topology

end Langlands.TopologicalInduction
