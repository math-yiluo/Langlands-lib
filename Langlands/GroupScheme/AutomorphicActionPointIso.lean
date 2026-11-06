import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Reductive.UnipotentRadicalAction
import Langlands.GroupScheme.Lie.ActionDifferential
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Evaluating an automorphic action at a base point -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S}
    (a : AutomorphicAction H G)

/-- A point over the base acts by an actual automorphism of the target group scheme. -/
def basePointIso (h : Over.mk (𝟙 S) ⟶ H.X) : G ≅ G :=
  a.sectionIso h

/-- The evaluated automorphism has the prescribed action on every test scheme. -/
theorem comp_basePointIso_hom (h : Over.mk (𝟙 S) ⟶ H.X)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (a.basePointIso h).hom.hom.hom =
      a.act (H.constantPoint h T) x :=
  a.comp_sectionIso_hom h x

section Differential

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] (a : AutomorphicAction H G)
    (h : Over.mk (𝟙 (Spec R)) ⟶ H.X)
    (A : Type u) [CommRing A] [Algebra R A]

/-- Differentiating evaluation agrees with evaluating the differential of the action. -/
theorem targetMapLinear_basePointIso (X : Additive (lieKernel G A)) :
    Lie.targetMapLinear (a.basePointIso h).hom A X =
      a.differential (H.constantPoint h _) X := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val ≫ (a.basePointIso h).hom.hom.hom = _
  rw [comp_basePointIso_hom, differential_val]
  congr 1
  exact (H.constantPoint_naturality h
    ((algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R A A)).op)).symm

end Differential

end Langlands.GroupScheme.AutomorphicAction
