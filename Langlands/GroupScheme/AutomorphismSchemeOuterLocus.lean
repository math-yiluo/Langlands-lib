import Langlands.GroupScheme.IsomorphismSchemeGroup
import Langlands.GroupScheme.OuterIsomorphismSchemeOrbit

/-! # The inner action classifier from its outer identity fibre -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G A : GroupScheme S}
  (I : GroupIsomorphismScheme G G)

/-- The global point of the supplied representer corresponding to the identity. -/
def identityPoint : Over.mk (𝟙 S) ⟶ I.parameter :=
  (1 : Over.mk (𝟙 S) ⟶ I.automorphismGroup.X)

@[simp] theorem universalIso_identityPoint {T : Over S} (g : T ⟶ G.X) :
    I.universalIso.toFun (toUnit T ≫ I.identityPoint) g = g := by
  let : GrpObj I.parameter := I.automorphismGroup.grp
  change I.universalIso.toFun
    (toUnit T ≫ (1 : Over.mk (𝟙 S) ⟶ I.automorphismGroup.X)) g = g
  rw [MonObj.comp_one, I.universalIso_one]

theorem toGroupAutomorphismScheme_classifyAction_eval (a : AutomorphicAction A G)
    {T : Over S} (d : T ⟶ A.X) (g : T ⟶ G.X) :
    I.universalIso.toFun
      (d ≫ (I.toGroupAutomorphismScheme.classifyAction a).hom.hom) g = a.act d g := by
  have h := congrArg (fun b : AutomorphicAction A G => b.act d g)
    (I.toGroupAutomorphismScheme.action_restrict_classifyAction a)
  rw [AutomorphicAction.restrict_act] at h
  change I.evaluationAction.act
    (d ≫ (I.toGroupAutomorphismScheme.classifyAction a).hom.hom) g = a.act d g at h
  simpa only [I.evaluationAction_act] using h

variable {a : AutomorphicAction A G} (O : OuterIsomorphismScheme I a)

/-- Inversion turns the inverse-precomposition identity orbit into the direct
homomorphism classifying the acting automorphisms. -/
theorem inv_comp_identityOrbit :
    ι[A.X] ≫ O.pointOrbit I.identityPoint =
      (I.toGroupAutomorphismScheme.classifyAction a).hom.hom := by
  apply I.hom_ext
  intro T t g
  rw [← Category.assoc, O.comp_pointOrbit, I.actionHom_eval,
    I.universalIso_identityPoint, I.toGroupAutomorphismScheme_classifyAction_eval]
  change a.act (t⁻¹)⁻¹ g = a.act t g
  rw [inv_inv]

/-- The direct action classifier is open whenever its supplied outer parameter
is étale over the base. -/
theorem classifyAction_isOpenImmersion [Etale O.parameter.hom] :
    IsOpenImmersion (I.toGroupAutomorphismScheme.classifyAction a).hom.hom.left := by
  have : IsIso ι[A.X].left := (Over.forget S).map_isIso ι[A.X]
  have := O.pointOrbit_isOpenImmersion I.identityPoint
  rw [← I.inv_comp_identityOrbit O]
  change IsOpenImmersion (ι[A.X].left ≫ (O.pointOrbit I.identityPoint).left)
  infer_instance

/-- The direct action classifier is closed whenever its supplied outer parameter
is separated over the base. -/
theorem classifyAction_isClosedImmersion [IsSeparated O.parameter.hom] :
    IsClosedImmersion (I.toGroupAutomorphismScheme.classifyAction a).hom.hom.left := by
  have : IsIso ι[A.X].left := (Over.forget S).map_isIso ι[A.X]
  have := O.pointOrbit_isClosedImmersion I.identityPoint
  rw [← I.inv_comp_identityOrbit O]
  change IsClosedImmersion (ι[A.X].left ≫ (O.pointOrbit I.identityPoint).left)
  infer_instance

end Langlands.GroupScheme.GroupIsomorphismScheme
