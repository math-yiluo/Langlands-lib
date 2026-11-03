import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Restricting a supplied homogeneous quotient to a closed subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientRestriction

variable {S : Scheme.{u}} {G H P K : GroupScheme S}
variable (d : H ⟶ G) (i : P ⟶ G)

/-- Multiplication of the actual subgroup and stabilizer in the ambient group. -/
def productMap : H.X ⊗ P.X ⟶ G.X :=
  (fst _ _ ≫ d.hom.hom) * (snd _ _ ≫ i.hom.hom)

variable {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (a b : T ⟶ G.X),
  a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)

include hfib in
/-- Right multiplication by the stabilizer disappears under the supplied map. -/
theorem productMap_comp :
    productMap d i ≫ q = fst H.X P.X ≫ (d.hom.hom ≫ q) := by
  apply Eq.symm
  apply (hfib (H.X ⊗ P.X) (fst _ _ ≫ d.hom.hom) (productMap d i)).mpr
  change (fst _ _ ≫ d.hom.hom)⁻¹ *
    ((fst _ _ ≫ d.hom.hom) * (snd _ _ ≫ i.hom.hom)) ∈ _
  rw [inv_mul_cancel_left]
  exact SubgroupFunctor.mem_range.mpr ⟨snd _ _, rfl⟩

include hfib in
/-- Restriction preserves the exact right-coset relation for the full preimage
of the original stabilizer, on every relative scheme test. -/
theorem fibers (j : K ⟶ H)
    (hpre : SubgroupFunctor.range j = (SubgroupFunctor.range i).comap d)
    (T : Over S) (a b : T ⟶ H.X) :
    a ≫ (d.hom.hom ≫ q) = b ≫ (d.hom.hom ≫ q) ↔
      a⁻¹ * b ∈ (SubgroupFunctor.range j).carrier T := by
  rw [← Category.assoc, ← Category.assoc, hfib, hpre,
    SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp]

section Geometry

variable [Mono i.hom.hom] [Smooth q.left]

include hfib in
/-- A smooth subgroup-stabilizer multiplication map makes the restricted
projection smooth. Smoothness of the stabilizer follows from the original
exact smooth quotient. -/
theorem smooth [Smooth (productMap d i).left] :
    Smooth (d.hom.hom ≫ q).left := by
  let : Smooth P.X.hom :=
    HomogeneousQuotient.smooth_subgroup_of_smooth_quotient G P i q hfib
  have hfst : Smooth (fst H.X P.X).left := by
    change Smooth (pullback.fst H.X.hom P.X.hom)
    infer_instance
  have hsurj : Surjective (fst H.X P.X).left := by
    constructor
    intro x
    refine ⟨(lift (𝟙 H.X) (1 : H.X ⟶ P.X)).left x, ?_⟩
    exact congrArg (fun f : H.X ⟶ H.X => f.left x) (lift_fst _ _)
  have he : (fst H.X P.X).left ≫ (d.hom.hom ≫ q).left =
      (productMap d i).left ≫ q.left :=
    (congrArg (fun f => f.left) (productMap_comp d i q hfib)).symm
  have : Smooth ((fst H.X P.X).left ≫ (d.hom.hom ≫ q).left) := by
    rw [he]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    (fst H.X P.X).left (d.hom.hom ≫ q).left

end Geometry

include hfib in
/-- Surjective subgroup-stabilizer multiplication and a surjective original
projection make the restricted projection surjective. -/
theorem surjective [Surjective q.left] [Surjective (productMap d i).left] :
    Surjective (d.hom.hom ≫ q).left := by
  have he : (fst H.X P.X).left ≫ (d.hom.hom ≫ q).left =
      (productMap d i).left ≫ q.left :=
    (congrArg (fun f => f.left) (productMap_comp d i q hfib)).symm
  have : Surjective ((fst H.X P.X).left ≫ (d.hom.hom ≫ q).left) := by
    rw [he]
    infer_instance
  exact Surjective.of_comp (fst H.X P.X).left (d.hom.hom ≫ q).left

/-- A closed subgroup restriction of a quasi-compact projection is
quasi-compact. -/
theorem quasiCompact (hd : IsClosedSubgroup d) [QuasiCompact q.left] :
    QuasiCompact (d.hom.hom ≫ q).left := by
  let : IsClosedImmersion d.hom.hom.left := hd
  change QuasiCompact (d.hom.hom.left ≫ q.left)
  infer_instance

/-- The supplied quotient target itself is a homogeneous quotient of the
subgroup by the represented full-preimage stabilizer, provided multiplication
by the original stabilizer is smooth and surjective. -/
def restrict (hd : IsClosedSubgroup d) [Mono i.hom.hom]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [Smooth (productMap d i).left] [Surjective (productMap d i).left]
    (j : K ⟶ H)
    (hpre : SubgroupFunctor.range j = (SubgroupFunctor.range i).comap d) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j where
  scheme := Q
  projection := d.hom.hom ≫ q
  separated := inferInstance
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance
  smooth_projection := smooth d i q hfib
  surjective_projection := surjective d i q hfib
  quasiCompact_projection := quasiCompact d q hd
  fibers := fibers d i q hfib j hpre

end Langlands.GroupScheme.HomogeneousQuotientRestriction
