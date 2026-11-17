import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantPresheaf
import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantDualAmpleStatement
import Langlands.AlgebraicGeometry.Picard.FiniteCoproductAmple

/-! # The actual parabolic Lie determinant on quotient components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

section Coproduct

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {I : Type u} (V : I → Over S)
    (F : ∀ i, ParabolicSubgroup ((baseChange (V i).hom).obj G))

/-- The actual determinant dual of a glued parabolic family restricts to the
actual determinant dual of its prescribed component family. -/
def coproductParabolicLieDeterminantDualPullbackIso (i : I) :
    (LineBundle.pullback (sigmaOverι V i).left).obj
        (parabolicRepresentative (coproductParabolic hG V F)).lieDeterminant.dual ≅
      (parabolicRepresentative (F i)).lieDeterminant.dual :=
  LineBundle.dualPullbackIso (sigmaOverι V i).left _ ≪≫
    LineBundle.dualIso (parabolicLieDeterminantPullbackIso hG (sigmaOverι V i)
      (coproductParabolic hG V F) (F i) (restrict_coproductParabolic hG V F i))

end Coproduct

section FiniteAffine

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Finite I] {P : I → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))

/-- The component inclusion identifies the actual determinant dual in the
finite target with the actual dual on the homogeneous quotient family. -/
def finiteAffineParabolicLieDeterminantDualPullbackIso (a : I) :
    (LineBundle.pullback
        (sigmaOverι (affineParabolicQuotientComponents hG j hj) a).left).obj
        (parabolicRepresentative (finiteAffineParabolicFamily hG j hj)).lieDeterminant.dual ≅
      (parabolicRepresentative
        (affineParabolicQuotientFamilies hG j hj a)).lieDeterminant.dual :=
  coproductParabolicLieDeterminantDualPullbackIso hG
    (affineParabolicQuotientComponents hG j hj)
    (affineParabolicQuotientFamilies hG j hj) a

/-- Ampleness of the precise finite-target bundle is equivalent to ampleness
of the precise actual quotient-family bundle on each component. -/
theorem finiteAffineParabolicLieDeterminantDual_isAmple_iff :
    (parabolicRepresentative (finiteAffineParabolicFamily hG j hj)).lieDeterminant.dual.IsAmple ↔
      ∀ a, (parabolicRepresentative
        (affineParabolicQuotientFamilies hG j hj a)).lieDeterminant.dual.IsAmple := by
  let : IsProper (finiteAffineParabolicQuotient hG j hj).val.hom :=
    (finiteAffineParabolicQuotient hG j hj).property.2
  let : CompactSpace (∐ fun a => (affineParabolicQuotientComponents hG j hj a).left :
      Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (finiteAffineParabolicQuotient hG j hj).val.hom
  let : QuasiSeparatedSpace
      (∐ fun a => (affineParabolicQuotientComponents hG j hj a).left : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (finiteAffineParabolicQuotient hG j hj).val.hom
  rw [LineBundle.isAmple_finite_coproduct_iff]
  apply forall_congr'
  intro a
  let e := (LineBundle.forget _).mapIso
    (finiteAffineParabolicLieDeterminantDualPullbackIso hG j hj a)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end FiniteAffine

/-- Positivity on each actual affine homogeneous quotient gives the unchanged
finite-family target, including an empty index type. -/
theorem finiteAffineParabolicDeterminantDualAmple_of_components
    (hample : ∀ (R : Type u) [CommRing R]
      (G P : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
      (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i),
      (parabolicRepresentative (homogeneousQuotientParabolic hG i hi
        (affineParabolicQuotient hG i hi).quotient)).lieDeterminant.dual.IsAmple) :
    FiniteAffineParabolicDeterminantDualAmpleStatement.{u} := by
  intro R _ G hG I _ P j hj
  apply (finiteAffineParabolicLieDeterminantDual_isAmple_iff hG j hj).mpr
  intro a
  exact hample R G (P a) hG (j a) (hj a)

end Langlands.GroupScheme.ParabolicSubgroupModuli
