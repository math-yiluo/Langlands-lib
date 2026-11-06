import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection
import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.Topology.Algebra.Module.Basic

/-! # Closed ideal extension and contraction on finite full-domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
  {C : Type z} [NormedCommRing C] [NormedAlgebra K C]

/-- Extension of an ideal with the actual target norm topology retained. -/
def closedIdealMap (f : BoundedAlgHom K A B) (I : Ideal A) : Ideal B :=
  (Ideal.map f.toAlgHom.toRingHom I).topologicalClosure

theorem isClosed_closedIdealMap (f : BoundedAlgHom K A B) (I : Ideal A) :
    IsClosed (f.closedIdealMap I : Set B) :=
  (Ideal.map f.toAlgHom.toRingHom I).isClosed_topologicalClosure

theorem mem_closedIdealMap (f : BoundedAlgHom K A B) {I : Ideal A} {a : A}
    (ha : a ∈ I) : f a ∈ f.closedIdealMap I :=
  (Ideal.map f.toAlgHom.toRingHom I).le_topologicalClosure
    (Ideal.mem_map_of_mem f.toAlgHom.toRingHom ha)

/-- Closed extension is left adjoint to contraction into a closed ideal. -/
theorem closedIdealMap_le_iff (f : BoundedAlgHom K A B) (I : Ideal A)
    (J : Ideal B) (hJ : IsClosed (J : Set B)) :
    f.closedIdealMap I ≤ J ↔ I ≤ Ideal.comap f.toAlgHom.toRingHom J := by
  constructor
  · intro h a ha
    exact h (f.mem_closedIdealMap ha)
  · intro h
    exact (Ideal.map f.toAlgHom.toRingHom I).topologicalClosure_minimal
      (Ideal.map_le_iff_le_comap.mpr h) hJ

theorem closedIdealMap_mono (f : BoundedAlgHom K A B) {I J : Ideal A}
    (h : I ≤ J) : f.closedIdealMap I ≤ f.closedIdealMap J :=
  Submodule.topologicalClosure_mono (Ideal.map_mono h)

/-- Closed extension respects composition of the actual bounded maps. -/
theorem closedIdealMap_comp (f : BoundedAlgHom K A B) (g : BoundedAlgHom K B C)
    (I : Ideal A) :
    g.closedIdealMap (f.closedIdealMap I) = (g.comp f).closedIdealMap I := by
  apply le_antisymm
  · apply (g.closedIdealMap_le_iff _ _ ((g.comp f).isClosed_closedIdealMap I)).mpr
    apply (f.closedIdealMap_le_iff _ _
      (((g.comp f).isClosed_closedIdealMap I).preimage g.continuous)).mpr
    intro a ha
    exact (g.comp f).mem_closedIdealMap ha
  · apply ((g.comp f).closedIdealMap_le_iff _ _
      (g.isClosed_closedIdealMap (f.closedIdealMap I))).mpr
    intro a ha
    exact g.mem_closedIdealMap (f.mem_closedIdealMap ha)

end BoundedAlgHom

namespace PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A} (c : FiniteCover U)

/-- The global ideal of sections lying in every supplied local ideal. -/
def idealContraction (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) : Ideal U.algebra :=
  ⨅ i, Ideal.comap (c.map i).restriction.toAlgHom.toRingHom (I i)

@[simp]
theorem mem_idealContraction (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra)
    (a : U.algebra) :
    a ∈ c.idealContraction I ↔ ∀ i, (c.map i).restriction a ∈ I i :=
  Ideal.mem_iInf

/-- The contraction is closed in the original target algebra norm. -/
theorem isClosed_idealContraction (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra)
    (hI : ∀ i, IsClosed (I i : Set (c.obj i).algebra)) :
    IsClosed (c.idealContraction I : Set U.algebra) := by
  have heq : (c.idealContraction I : Set U.algebra) =
      ⋂ i, (c.map i).restriction ⁻¹' (I i : Set (c.obj i).algebra) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, mem_idealContraction]
  rw [heq]
  exact isClosed_iInter fun i => (hI i).preimage (c.map i).restriction.continuous

/-- The elementary direction of effectiveness needs no overlap compatibility. -/
theorem closedIdealMap_idealContraction_le
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra)
    (hI : ∀ i, IsClosed (I i : Set (c.obj i).algebra)) (i : Fin c.size) :
    (c.map i).restriction.closedIdealMap (c.idealContraction I) ≤ I i :=
  ((c.map i).restriction.closedIdealMap_le_iff _ _ (hI i)).mpr (iInf_le _ i)

/-- The explicit contraction is the largest global ideal whose closed extensions
lie in all the given local ideals. -/
theorem le_idealContraction_iff
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra)
    (hI : ∀ i, IsClosed (I i : Set (c.obj i).algebra)) (J : Ideal U.algebra) :
    J ≤ c.idealContraction I ↔
      ∀ i, (c.map i).restriction.closedIdealMap J ≤ I i := by
  simp only [idealContraction, le_iInf_iff,
    BoundedAlgHom.closedIdealMap_le_iff _ _ _ (hI _)]

/-- Equality of closed extensions on the actual presented intersections of
cover members. Both restriction maps are the original pushout legs. -/
def IdealCompatible (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra) : Prop :=
  ∀ i j, ((c.obj i).interLeft (c.obj j)).restriction.closedIdealMap (I i) =
    ((c.obj i).interRight (c.obj j)).restriction.closedIdealMap (I j)

/-- A global ideal always gives overlap-compatible closed local extensions. -/
theorem idealCompatible_closedIdealMap (J : Ideal U.algebra) :
    c.IdealCompatible (fun i => (c.map i).restriction.closedIdealMap J) := by
  intro i j
  rw [BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp]
  have heq : (c.obj i).interLeft (c.obj j) ≫ c.map i =
      (c.obj i).interRight (c.obj j) ≫ c.map j :=
    (inferInstance : Subsingleton (Inclusion _ _)).elim _ _
  rw [← Inclusion.restriction_comp, ← Inclusion.restriction_comp, heq]

end PresentedAffinoidAlgebra.Domain.FiniteCover
end Langlands.Analytic
