import Langlands.GroupScheme.Nilpotent.PerfectFieldProductStatement
import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.Rational.PerfectFieldSectionedSolvableQuotient
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Reductive.CommutingMultiplication

/-! # Products of unipotent groups and tori over perfect fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected affine group over a perfect field is geometrically nilpotent
if and only if it is a product of a smooth connected affine unipotent group and a torus. -/
theorem nilpotentPerfectFieldProduct : NilpotentPerfectFieldProductStatement.{u} := by
  intro k _ _ G hsm haff hconn
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let : ConnectedSpace G.X.left := hconn
  constructor
  · intro hG
    let D := perfectFieldSectionedSolvableTorusQuotient solvableTorusQuotient
      RelativeRoot.splitUnipotentStableVectorSubgroup G hG.isSolvableGroupScheme
    have hi := D.isGeometricUnipotentRadical.1
    let : IsClosedImmersion D.inclusion.hom.hom.left := hi.isClosedSubgroup
    let : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
    have hUaff : IsAffineHom D.source.X.hom := by
      rw [← Over.w D.inclusion.hom.hom]
      infer_instance
    let s := D.quotientData.sectionHom
    have hs : s ≫ D.quotientData.projection = 𝟙 D.quotientData.quotient :=
      D.quotientData.sectionHom_comp
    let : IsIso (s ≫ D.quotientData.projection) := by rw [hs]; infer_instance
    have hmul : IsIso (subgroupMultiplication s D.inclusion) :=
      isIso_subgroupMultiplication_of_isIso_comp inferInstance
        D.quotientData.isFppfQuotient.2.2.2
    have hc : IsCentral s := hG.isCentral_of_isTorus D.torus D.torus_isTorus s
    let m := commutingSubgroupMultiplicationHom s D.inclusion
      (fun T t u => commute_of_mem_center (hc T t) (u ≫ D.inclusion.hom.hom))
    let : IsIso m.hom.hom := hmul
    let : IsIso ((Mon.forget _).map m.hom) := ‹IsIso m.hom.hom›
    let : IsIso m.hom := isIso_of_reflects_iso m.hom (Mon.forget _)
    let : IsIso ((Grp.forget₂Mon _).map m) := ‹IsIso m.hom›
    let : IsIso m := isIso_of_reflects_iso m (Grp.forget₂Mon _)
    exact ⟨D.source, D.torus.toGrp, hi.smooth, hUaff, hi.connectedSpace,
      hi.isUnipotent, D.torus_isTorus,
      ⟨(asIso m).symm ≪≫ β_ D.torus.toGrp D.source⟩⟩
  · rintro ⟨U, T, hUsm, hUaff, _hUconn, hU, hT, ⟨e⟩⟩
    let : Smooth U.X.hom := hUsm
    let : IsAffineHom U.X.hom := hUaff
    let : IsCommMonObj T.X := hT.isCommMonObj
    let P := (Over.map (toAlgebraicClosure k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
    let : Group.IsNilpotent (P ⟶ U.X) := isNilpotent_points_of_isUnipotent hU P
    have hprod : Group.IsNilpotent ((P ⟶ U.X) × (P ⟶ T.X)) := inferInstance
    have hpoints : Group.IsNilpotent (P ⟶ G.X) :=
      (Group.isNilpotent_congr ((isoPointsEquiv e P).trans
        (productPointsEquiv U T P))).2 hprod
    exact (Group.isNilpotent_congr (baseChangePointsEquiv (toAlgebraicClosure k) G
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))).2 hpoints

end Langlands.GroupScheme
