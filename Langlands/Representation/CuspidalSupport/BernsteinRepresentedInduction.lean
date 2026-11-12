import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Exponents.StandardCuspidalInductionCompression

/-! # Comparing actual represented and Bernstein standard induction -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinRepresentedInductionInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinRepresentedInductionInstance2 : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinRepresentedInductionInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinRepresentedInductionInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinRepresentedInductionInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinRepresentedInductionInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinRepresentedInductionInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Actual represented induction from the original standard rational Levi. -/
def bernsteinStandardRepresentedInductionFunctor (I : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  let h := bernsteinStandardRepresentativesGeometric i ν family I
  RepresentedParabolic.leviInductionFunctor
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    h.1 h.2.2.1 h.2.1 h.2.2.2

/-- The represented and literal standard inductions agree on every original
rational-Levi representation, independently of cuspidality. -/
def bernsteinStandardRepresentedInductionIso (I : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))) :
    (bernsteinStandardRepresentedInductionFunctor i ν family I).obj ρ ≅
      (normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).obj
        (bernsteinLiteralLeviRep i ν I ρ) := by
  let p := Standard.parabolicHom i ν (rootSet i ν I)
  let l := Standard.leviToParabolic i ν (rootSet i ν I)
  let r := Standard.unipotentToParabolic i ν (rootSet i ν I)
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family I
  let hR := RepresentedParabolic.isSemidirectDecomposition_pointImage
    p l r hgeom.1.isClosedSubgroup hgeom.2.2.1 hgeom.2.2.2
  let hUR := RepresentedParabolic.isClosed_pointImage_comp
    p r hgeom.1.isClosedSubgroup hgeom.2.2.1.1.isClosedSubgroup
  have he (x : rationalPoints (bernsteinLeviScheme i ν I)) :
      (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1 x :
        rationalPoints G) = (leviRationalPointHomeomorph i ν I x : rationalPoints G) := by
    rw [RepresentedParabolic.leviPointsEquiv_apply_coe,
      leviRationalPointHomeomorph_apply_coe]
    change rationalPoints.map
      (Standard.leviToParabolic i ν (rootSet i ν I) ≫
        Standard.parabolicHom i ν (rootSet i ν I)) x = _
    rw [Standard.leviToParabolic_comp]
  let c := rationalInertiaInductionIsoOfEmbeddedLevi (bernsteinLeviScheme i ν I)
    (H := rationalPoints G)
    (P := RepresentedParabolic.pointImage p)
    (M := RepresentedParabolic.pointImage (l ≫ p))
    (U := RepresentedParabolic.pointImage (r ≫ p))
    (P' := parabolic i ν I) (M' := levi i ν I) (U' := unipotent i ν I)
    (standardCompression_parabolicPoints i ν I) (standardCompression_leviPoints i ν I)
    (standardCompression_unipotentPoints i ν I) hR hUR
    (family.decomposition I) (family.closedUnipotent I)
    (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1).symm
    (leviRationalPointHomeomorph i ν I).symm he ρ
  dsimp only [bernsteinStandardRepresentedInductionFunctor,
    RepresentedParabolic.leviInductionFunctor, RepresentedParabolic.inductionFunctor,
    Functor.comp_obj]
  simpa only [rationalInertiaInductionFunctor, Functor.comp_obj,
    SmoothRep.pullbackFunctor, bernsteinLiteralLeviRep] using c

/-- Induction of the original actual datum through the represented interface. -/
def bernsteinRepresentedInduction
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  (bernsteinStandardRepresentedInductionFunctor i ν family a.roots).obj a.representation

/-- The represented induction of a datum is its original Bernstein induction. -/
def bernsteinRepresentedInductionIso
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    bernsteinRepresentedInduction i ν family a ≅ bernsteinInduction i ν family a :=
  bernsteinStandardRepresentedInductionIso i ν family a.roots a.representation

end Langlands.CuspidalSupport
