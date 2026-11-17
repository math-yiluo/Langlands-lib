import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionAssembly

/-! # Inertial-support uniqueness from Bernstein decomposition -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.CuspidalSupport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance supportUniquenessFromDecompositionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance supportUniquenessFromDecompositionTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- A published Bernstein decomposition theorem, instantiated at the common
carrier universe, also discharges inertial-support uniqueness for this family. -/
theorem bernsteinInertialSupportUniqueness_of_bernsteinDecomposition
    (hBernstein : BernsteinDecompositionStatement.{uF,max uF uV}) :
    BernsteinInertialSupportUniquenessStatement.{uF,uV} i ν family :=
  bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero i ν family
    (hBernstein F G T i ν family).2

set_option linter.defProp false in
/-- The reduction from Bernstein decomposition to support uniqueness as a
defined proof term. -/
def bernsteinInertialSupportUniquenessFromDecomposition
    (hBernstein : BernsteinDecompositionStatement.{uF,max uF uV}) :
    BernsteinInertialSupportUniquenessStatement.{uF,uV} i ν family :=
  bernsteinInertialSupportUniqueness_of_bernsteinDecomposition i ν family hBernstein

end Langlands.CuspidalSupport
