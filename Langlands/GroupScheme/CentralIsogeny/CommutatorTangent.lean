import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.Adjoint

/-! # Lifting adjoint differences through a central isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CommutatorDescent

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  (q : G ⟶ H) (hq : IsCentral (kernelι q))
  [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- A source point and a target infinitesimal determine a source infinitesimal
by the descended commutator. -/
def tangentLift (n : Lie.AffinePoints G A) (X : lieKernel H A) : lieKernel G A :=
  ⟨lift (Lie.constant H (n ≫ q.hom.hom)) X.val ≫ hom q hq, by
    change Lie.reduction G _ = 1
    change (algSpec R).map
      (Opposite.op (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A))) ≫
        (lift (Lie.constant H (n ≫ q.hom.hom)) X.val ≫
          hom q hq) = 1
    rw [comp_lift_assoc]
    change lift (Lie.reduction H (Lie.constant H (n ≫ q.hom.hom)))
      (Lie.reduction H X.val) ≫ hom q hq = 1
    rw [Lie.reduction_constant, X.property]
    have h := lift_hom q hq n (1 : Lie.AffinePoints G A)
    simpa only [MonObj.one_comp, mul_one, inv_one, mul_inv_cancel] using h⟩

@[simp]
theorem tangentLift_val (n : Lie.AffinePoints G A) (X : lieKernel H A) :
    (tangentLift q hq n X).val =
      lift (Lie.constant H (n ≫ q.hom.hom)) X.val ≫ hom q hq := rfl

/-- The actual differential sends the lift to the adjoint difference. -/
theorem targetMap_tangentLift (n : Lie.AffinePoints G A) (X : lieKernel H A) :
    Lie.targetMap q A (tangentLift q hq n X) =
      lieKernelConjugation H (n ≫ q.hom.hom) X * X⁻¹ := by
  apply Subtype.ext
  change (lift (Lie.constant H (n ≫ q.hom.hom)) X.val ≫
      hom q hq) ≫ q.hom.hom =
    Lie.constant H (n ≫ q.hom.hom) * X.val *
      (Lie.constant H (n ≫ q.hom.hom))⁻¹ * X.val⁻¹
  rw [Category.assoc, hom_comp, commutatorMap_lift]
  simp only [Grp.id_hom_hom, Category.comp_id]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Every difference of a target tangent vector and its conjugate by a source
point has an actual differential preimage. -/
theorem targetMapLinear_tangentLift (n : Lie.AffinePoints G A)
    (X : Additive (lieKernel H A)) :
    Lie.targetMapLinear q A (Additive.ofMul (tangentLift q hq n X.toMul)) =
      adjoint H A (n ≫ q.hom.hom) X - X := by
  apply Additive.toMul.injective
  exact targetMap_tangentLift q hq n X.toMul

include hq in
/-- The range of the actual differential contains the range of every adjoint
difference induced by a source point. -/
theorem range_adjoint_sub_id_le (n : Lie.AffinePoints G A) :
    LinearMap.range (adjoint H A (n ≫ q.hom.hom) - LinearMap.id) ≤
      LinearMap.range (Lie.targetMapLinear q A) := by
  rintro _ ⟨X, rfl⟩
  exact ⟨Additive.ofMul (tangentLift q hq n X.toMul),
    targetMapLinear_tangentLift q hq n X⟩

omit [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] in
/-- Every central isogeny satisfies the adjoint-difference range containment. -/
theorem range_adjoint_sub_id_le_of_centralIsogeny (hqi : IsCentralIsogeny q)
    (n : Lie.AffinePoints G A) :
    LinearMap.range (adjoint H A (n ≫ q.hom.hom) - LinearMap.id) ≤
      LinearMap.range (Lie.targetMapLinear q A) := by
  let := hqi.isFinite
  let := hqi.flat
  let := hqi.surjective
  exact range_adjoint_sub_id_le q hqi.isCentral_kernelι n

end Langlands.GroupScheme.CommutatorDescent
