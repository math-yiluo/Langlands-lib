import Langlands.Representation.Aubert.General.CanonicalRationalSharpReductionStatements
import Langlands.Representation.Aubert.General.RationalStandardFiniteLength
import Langlands.Representation.Aubert.General.SharpFiniteLength

/-! # Proof of the reduction of canonical Sharp finite length -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- The two dynamic finite-length targets at carrier universe `max (u + 1) v`
imply finite length of the canonical actual terminal cokernel. -/
theorem canonicalRationalSharpFiniteLengthReduction :
    CanonicalRationalSharpFiniteLengthReductionStatement.{u, v} := by
  intro hiDyn hrDyn k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let _ : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : Smooth G.X.hom := hG.smooth
  let _ : T2Space k := BruhatTits.localField_t2Space k
  let _ : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let _ : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let _ : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  intro ν hν
  let _ := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  intro _
  exact sharpFiniteLengthTarget_of_inductionJacquet _ _ _ _ _ _ _ _
    (fun J => standardInductionJacquet_preservesFiniteLength_of_dynamic
      i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiDyn hrDyn J)

end Langlands.Aubert.General.RationalPointFamily
