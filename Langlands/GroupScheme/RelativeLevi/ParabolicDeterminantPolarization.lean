import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantPresheaf
import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantDualAmpleStatement
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleLocalModels
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleAmple

/-! # The actual determinant dual on finite parabolic representing models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.Picard

section BaseChange

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- The same actual representative, viewed in the directly pulled-back ambient
group using the standard iterated pullback comparison. -/
def ParabolicRepresentative.pushBase (b : S' ⟶ S) {T : Over S'}
    {F : ParabolicSubgroup ((baseChange T.hom).obj ((baseChange b).obj G))}
    (r : ParabolicRepresentative F) :
    ParabolicRepresentative (baseChangeEquiv b T F) where
  group := r.group
  hom := TorusSubgroupModuli.pushFamily b r.hom
  parabolic := r.parabolic.comp_iso
    (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl G)
  represents := ⟨(r.parabolic.comp_iso
      (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl G)).mono,
    (baseChangeEquiv_range b F r.hom r.represents.2).symm⟩

/-- Restricting the original coherent determinant dual and changing the ambient
base give isomorphic actual line bundles on every family. -/
def parabolicLieDeterminantDualBaseChangeIso (b : S' ⟶ S) (hG : IsReductive G)
    {T : Over S'}
    (F : ParabolicSubgroup ((baseChange T.hom).obj ((baseChange b).obj G))) :
    ((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange b).bundle T
        ((parabolicPresheafBaseChangeIso b hG).hom.app (op T) F) ≅
      (parabolicLieDeterminantDualPresheafLineBundle
        ((baseChange b).obj G) (hG.baseChange b)).bundle T F :=
  parabolicLieDeterminantDualRepresentativeIso hG (baseChangeEquiv b T F)
    ((parabolicRepresentative F).pushBase b)

/-- The same comparison on the universal family of any supplied representer.
Both sides are line bundles on exactly the same parameter scheme. -/
def parabolicLieDeterminantDualUniversalBaseChangeIso
    (b : S' ⟶ S) (hG : IsReductive G) {M : Over S'}
    (e : (parabolicPresheaf ((baseChange b).obj G)
      (hG.baseChange b)).RepresentableBy M) :
    ((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange b).universal
        (e.ofIso (parabolicPresheafBaseChangeIso b hG)) ≅
      (parabolicLieDeterminantDualPresheafLineBundle
        ((baseChange b).obj G) (hG.baseChange b)).universal e :=
  parabolicLieDeterminantDualBaseChangeIso b hG (e.homEquiv (𝟙 M))

/-- The original coherent determinant dual is ample on the restricted
representer exactly when the pulled-back group's actual dual is ample there. -/
theorem parabolicLieDeterminantDual_universalBaseChange_isAmple_iff
    (b : S' ⟶ S) (hG : IsReductive G) {M : Over S'}
    (e : (parabolicPresheaf ((baseChange b).obj G)
      (hG.baseChange b)).RepresentableBy M) :
    (((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange b).universal
      (e.ofIso (parabolicPresheafBaseChangeIso b hG))).IsAmple ↔
    ((parabolicLieDeterminantDualPresheafLineBundle
      ((baseChange b).obj G) (hG.baseChange b)).universal e).IsAmple := by
  let c := (LineBundle.forget M.left).mapIso
    (parabolicLieDeterminantDualUniversalBaseChangeIso b hG e)
  exact ⟨fun h => h.of_iso c, fun h => h.of_iso c.symm⟩

end BaseChange

section FiniteAffine

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Finite I] {P : I → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))
    (htypes : HasUniformParabolicFieldTypes j)

/-- The actual finite quotient representation classifies its prescribed
coproduct family at the identity parameter. -/
@[simp]
theorem finiteAffineParabolicRepresentation_universal :
    (finiteAffineParabolicRepresentation hG j hj htypes).homEquiv (𝟙 _) =
      finiteAffineParabolicFamily hG j hj := by
  change restrict hG (𝟙 _) (finiteAffineParabolicFamily hG j hj) = _
  exact restrict_id hG _

/-- The coherent universal determinant dual on the finite quotient model is
exactly the actual dual determinant named by the positivity statement. -/
@[simp]
theorem finiteAffineParabolicDeterminantDual_universal :
    (parabolicLieDeterminantDualPresheafLineBundle G hG).universal
      (finiteAffineParabolicRepresentation hG j hj htypes) =
    (parabolicRepresentative (finiteAffineParabolicFamily hG j hj)).lieDeterminant.dual := by
  unfold PresheafLineBundle.universal
  rw [finiteAffineParabolicRepresentation_universal]
  rfl

/-- The focused actual positivity premise makes this same coherent
determinant dual ample on the finite quotient representation. -/
theorem finiteAffineParabolicDeterminantDual_universal_isAmple
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u}) :
    ((parabolicLieDeterminantDualPresheafLineBundle G hG).universal
      (finiteAffineParabolicRepresentation hG j hj htypes)).IsAmple := by
  rw [finiteAffineParabolicDeterminantDual_universal]
  exact hample R G hG I P j hj

include j hj htypes in
/-- Under the same focused positivity premise, the coherent determinant dual
is intrinsically ample and hence ample on any representing scheme. -/
theorem parabolicLieDeterminantDual_isAmple_of_finiteAffine
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u}) :
    (parabolicLieDeterminantDualPresheafLineBundle G hG).IsAmple :=
  ⟨_, finiteAffineParabolicRepresentation hG j hj htypes,
    finiteAffineParabolicDeterminantDual_universal_isAmple hG j hj htypes hample⟩

include j hj htypes in
/-- The same conclusion for any supplied representer of the actual parabolic
presheaf over this affine base. -/
theorem parabolicLieDeterminantDual_universal_isAmple_of_finiteAffine
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    {M : Over (Spec (CommRingCat.of R))}
    (e : (parabolicPresheaf G hG).RepresentableBy M) :
    ((parabolicLieDeterminantDualPresheafLineBundle G hG).universal e).IsAmple :=
  ((parabolicLieDeterminantDualPresheafLineBundle G hG).isAmple_iff_universal e).mp
    (parabolicLieDeterminantDual_isAmple_of_finiteAffine hG j hj htypes hample)

end FiniteAffine

end Langlands.GroupScheme.ParabolicSubgroupModuli
