import Langlands.GroupScheme.Reductive.Basic

/-! # The scheme-theoretic derived subgroup functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H D : GroupScheme S}

namespace SubgroupFunctor

/-- A subgroup functor contains the commutators on every test scheme over the base. -/
def ContainsCommutators (F : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (x y : T ⟶ G.X), x * y * x⁻¹ * y⁻¹ ∈ F.carrier T

/-- A subgroup containing every commutator is normal on every test scheme. -/
theorem ContainsCommutators.isNormal {F : SubgroupFunctor G} (hF : F.ContainsCommutators) :
    F.IsNormal := by
  intro T g x _ hx
  have h := (F.carrier T).mul_mem (hF T g x) hx
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- All points contain every commutator. -/
theorem containsCommutators_top (G : GroupScheme S) :
    (⊤ : SubgroupFunctor G).ContainsCommutators :=
  fun _ _ _ => Subgroup.mem_top _

/-- The identity homomorphism has the total subgroup functor as its range. -/
@[simp] theorem range_id (G : GroupScheme S) : range (𝟙 G) = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    exact Subgroup.mem_top _
  · intro _
    exact ⟨x, Category.comp_id x⟩

end SubgroupFunctor

/-- The scheme-theoretic derived subgroup functor: the pointwise intersection of the ranges of
all actual closed subgroup homomorphisms containing the commutators on every test scheme.
This definition does not assert that the intersection is represented by a group scheme. -/
def derivedSubgroup (G : GroupScheme S) : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∀ (H : GroupScheme S) (i : H ⟶ G), IsClosedSubgroup i →
          (SubgroupFunctor.range i).ContainsCommutators → x ∈ (SubgroupFunctor.range i).carrier T}
      one_mem' := fun _ i _ _ => ((SubgroupFunctor.range i).carrier T).one_mem
      mul_mem' := fun hx hy H i hc hcomm =>
        ((SubgroupFunctor.range i).carrier T).mul_mem (hx H i hc hcomm) (hy H i hc hcomm)
      inv_mem' := fun hx H i hc hcomm =>
        ((SubgroupFunctor.range i).carrier T).inv_mem (hx H i hc hcomm) }
  comp_mem a _ hx H i hc hcomm := (SubgroupFunctor.range i).comp_mem a (hx H i hc hcomm)

/-- Membership in the derived subgroup tests every closed commutator-containing subgroup. -/
theorem mem_derivedSubgroup {T : Over S} {x : T ⟶ G.X} :
    x ∈ (derivedSubgroup G).carrier T ↔
      ∀ (H : GroupScheme S) (i : H ⟶ G), IsClosedSubgroup i →
        (SubgroupFunctor.range i).ContainsCommutators → x ∈ (SubgroupFunctor.range i).carrier T :=
  Iff.rfl

/-- The total subgroup is an admissible member of the defining intersection. -/
theorem derivedSubgroup_total_admissible (G : GroupScheme S) :
    IsClosedSubgroup (𝟙 G) ∧ (SubgroupFunctor.range (𝟙 G)).ContainsCommutators := by
  constructor
  · change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  · rw [SubgroupFunctor.range_id]
    exact SubgroupFunctor.containsCommutators_top G

/-- Every commutator belongs to the scheme-theoretic derived subgroup on every test scheme. -/
theorem derivedSubgroup_containsCommutators (G : GroupScheme S) :
    (derivedSubgroup G).ContainsCommutators :=
  fun T x y _ _ _ hcomm => hcomm T x y

/-- The derived subgroup is contained in every closed subgroup containing all commutators. -/
theorem derivedSubgroup_le_range (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hcomm : (SubgroupFunctor.range i).ContainsCommutators) :
    derivedSubgroup G ≤ SubgroupFunctor.range i :=
  fun _ _ hx => hx H i hi hcomm

/-- The scheme-theoretic derived subgroup is normal on every test scheme. -/
theorem derivedSubgroup_isNormal (G : GroupScheme S) : (derivedSubgroup G).IsNormal :=
  (derivedSubgroup_containsCommutators G).isNormal

/-- An actual homomorphism exhibits the scheme-theoretic derived subgroup if it is a closed
subgroup and its full range functor is the defining intersection. -/
def IsDerivedSubgroup (d : D ⟶ G) : Prop :=
  IsClosedSubgroup d ∧ SubgroupFunctor.range d = derivedSubgroup G

namespace IsDerivedSubgroup

/-- An exhibiting closed inclusion represents the derived subgroup in the published sense. -/
theorem isRepresentedBy {d : D ⟶ G} (hd : IsDerivedSubgroup d) :
    (derivedSubgroup G).IsRepresentedBy d := by
  have : IsClosedImmersion d.hom.hom.left := hd.1
  exact ⟨Over.mono_of_mono_left _, hd.2⟩

/-- The range of an exhibiting inclusion contains all commutators. -/
theorem containsCommutators {d : D ⟶ G} (hd : IsDerivedSubgroup d) :
    (SubgroupFunctor.range d).ContainsCommutators := by
  rw [hd.2]
  exact derivedSubgroup_containsCommutators G

/-- The range of an exhibiting inclusion is normal on every test scheme. -/
theorem isNormal {d : D ⟶ G} (hd : IsDerivedSubgroup d) :
    (SubgroupFunctor.range d).IsNormal :=
  hd.containsCommutators.isNormal

/-- Every exhibiting inclusion is contained in each closed commutator-containing subgroup. -/
theorem range_le {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hcomm : (SubgroupFunctor.range i).ContainsCommutators) :
    SubgroupFunctor.range d ≤ SubgroupFunctor.range i := by
  rw [hd.2]
  exact derivedSubgroup_le_range i hi hcomm

end IsDerivedSubgroup

end Langlands.GroupScheme
