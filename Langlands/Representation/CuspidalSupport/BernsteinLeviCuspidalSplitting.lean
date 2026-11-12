import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaCofan
import Langlands.Representation.CuspidalSupport.RationalLeviSplittingFromWhole

/-! # Actual Bernstein Levi splittings from whole-category decomposition -/

noncomputable section

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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Every actual standard Levi representation has a cuspidal/remainder
coproduct splitting for the literal proper-standard Jacquet tests. -/
def BernsteinLeviCuspidalSplittingProperty : Prop :=
  ∀ (J : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)),
    HasLeviCuspidalRemainderSplitting (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J) A

/-- The whole-category decomposition theorem gives the actual literal Levi
splittings; all geometric, intrinsic-root and topological inputs are proved. -/
theorem bernsteinLeviCuspidalSplitting_of_wholeStatement
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}) :
    BernsteinLeviCuspidalSplittingProperty.{uF, uV} i ν family := by
  intro J A
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom (bernsteinLeviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J)).isAffineHom
  let fam := bernsteinLeviStandardFamily i ν family J
  have := fam.maximalSplitTorus.isSplitSubtorus.mono
  have hRoots : HasRelativeRootSystem (bernsteinLeviTorus i ν J) :=
    relativeRootSystem F (bernsteinLeviScheme i ν J) fam.connectedReductive T
      (bernsteinLeviTorus i ν J) fam.maximalSplitTorus
  exact hasLeviCuspidalRemainderSplitting_of_wholeStatement hwhole
    G family.connectedReductive T i family.maximalSplitTorus ν
    standardCocharacter standardLeviIntersection family.genericCocharacter
    family.closedUnipotent J (family.closedLevi J) hRoots A

end Langlands.CuspidalSupport
