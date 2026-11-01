import Langlands.AlgebraicGeometry.Picard.GroupObjectTangentAddition
import Langlands.AlgebraicGeometry.Picard.TangentSpaceStalkDerivation
import Langlands.AlgebraicGeometry.Picard.RigidifiedDeformationClasses
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof

/-! # Actual universal rigidified parameter tangent and ordinary deformations -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.GeneralLinear.DualNumber
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k]

/-- The monoid tangent formula at any section proved to be the identity. -/
lemma rationalStalkDerivationPoint_add_of_one_eq
    (P : Over (Spec (CommRingCat.of k))) [MonObj P]
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) (he : 1 = e) :
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    ∀ D E, rationalStalkDerivationPoint P e (D + E) =
      rationalStalkDerivationPoint P e D * rationalStalkDerivationPoint P e E := by
  subst e
  exact rationalStalkDerivationPoint_add P

namespace RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules DualNumberThickening

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)
  {P : Over (Spec (CommRingCat.of k))}
  (L : relative f ε hε P) (hL : IsUniversal f ε hε L)

/-- The actual sheaf-defined tangent module of a universal rigidified parameter
is in bijection with actual ordinary first-order deformation classes. -/
def tangentDeformationEquiv :
    Langlands.Scheme.tangentSpaceAtPoint P (trivialParameter f ε hε L hL) ≃
      DeformationClasses preservation f :=
  (tangentSpaceAtPointDerivationEquiv P (trivialParameter f ε hε L hL)).toEquiv.trans
    ((rationalStalkDerivationTangentEquiv P.hom
      (trivialParameter f ε hε L hL).left
      (Over.w (trivialParameter f ε hε L hL))).trans
      ((firstOrderClassifyingEquiv f ε hε L hL).trans
        (firstOrderDeformationEquiv preservation f ε hε)))

@[simp]
lemma tangentDeformationEquiv_val
    (t : Langlands.Scheme.tangentSpaceAtPoint P (trivialParameter f ε hε L hL)) :
    (tangentDeformationEquiv preservation f ε hε L hL t).val =
      underlyingDualNumberClassEquiv preservation f ε hε
        (classifyingMap f ε hε L (dualNumberTest k)
          (rationalStalkDerivationPoint P (trivialParameter f ε hε L hL)
            (tangentSpaceAtPointDerivationEquiv P (trivialParameter f ε hε L hL) t))) :=
  rfl

/-- Addition in the actual tangent module corresponds to actual tensor product
of first-order line-bundle classes. -/
lemma tangentDeformationEquiv_add
    (t s : Langlands.Scheme.tangentSpaceAtPoint P (trivialParameter f ε hε L hL)) :
    tangentDeformationEquiv preservation f ε hε L hL (t + s) =
      tangentDeformationEquiv preservation f ε hε L hL t *
        tangentDeformationEquiv preservation f ε hε L hL s := by
  let := universalCommGrpObj preservation pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
    pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible f ε hε
    pullbackTensorComposition L hL
  let := classesCommGroup preservation pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
    pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible f ε hε (dualNumberTest k)
  let e := trivialParameter f ε hε L hL
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  have he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) = e :=
    one_eq_trivialParameter preservation pullbackTensorUnitCoherence
      explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
      pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible f ε hε
      pullbackTensorComposition L hL
  have hp := rationalStalkDerivationPoint_add_of_one_eq P e he
    (tangentSpaceAtPointDerivationEquiv P e t) (tangentSpaceAtPointDerivationEquiv P e s)
  apply Subtype.ext
  simp only [tangentDeformationEquiv_val, Subgroup.coe_mul]
  rw [map_add (tangentSpaceAtPointDerivationEquiv P e), hp]
  have hc := classifyingMap_mul preservation pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
    pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible f ε hε
    pullbackTensorComposition L hL (dualNumberTest k)
    (rationalStalkDerivationPoint P e (tangentSpaceAtPointDerivationEquiv P e t))
    (rationalStalkDerivationPoint P e (tangentSpaceAtPointDerivationEquiv P e s))
  rw [hc]
  exact underlyingDualNumberClassEquiv_tensor preservation f ε hε _ _

/-- The actual universal tangent/deformation comparison as an additive equivalence. -/
def tangentDeformationAddEquiv :
    Langlands.Scheme.tangentSpaceAtPoint P (trivialParameter f ε hε L hL) ≃+
      Additive (DeformationClasses preservation f) where
  toEquiv := (tangentDeformationEquiv preservation f ε hε L hL).trans
    Additive.ofMul
  map_add' := tangentDeformationEquiv_add preservation f ε hε L hL

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
