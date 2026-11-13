import Langlands.Representation.Aubert.General.CanonicalRationalOperator
import Langlands.Representation.Aubert.General.RationalCorrectedTheorem36
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # The actual smooth Aubert complex with published structural inputs -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hi : IsMaximalSplitTorus i)
  (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)

/-- The genuine normalized degree object on every smooth input, with published structural inputs. -/
abbrev canonicalRationalDegreeObject :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    type_of% (rationalDegreeObject i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν) E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalDegreeObject i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν) E q

/-- The actual quotient-induced differential in the chosen exterior coordinates. -/
abbrev canonicalRationalDifferential :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    type_of% (rationalDifferential i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalDifferential i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q

/-- The actual incoming image at any degree, including degree zero. -/
abbrev canonicalRationalBoundary :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    type_of% (rationalBoundary i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalBoundary i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q

/-- The actual smooth quotient by the incoming image at any truncation degree. -/
abbrev canonicalRationalTerminalObject :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    type_of% (Complex.terminalObject.{u, u, max (u + 1) v}
    (StandardComplex.removedFamily (parabolic i ν))
    (StandardComplex.removedFamily (levi i ν))
    (StandardComplex.removedFamily (unipotent i ν))
    (fun s => isSemidirectDecomposition_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν (Finset.univ \ s))
    (fun s => canonicalStandardUnipotent_isClosed hG i ν hi hν (Finset.univ \ s))
    (fun s => standardUnipotent_isUnimodular i ν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν standardCocharacter hG hi hν) (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone
      (standardParabolic_monotone i ν standardParabolicOrder hG hi hν))
    (StandardComplex.removedFamily_monotone
      (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)) E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  Complex.terminalObject.{u, u, max (u + 1) v}
    (StandardComplex.removedFamily (parabolic i ν))
    (StandardComplex.removedFamily (levi i ν))
    (StandardComplex.removedFamily (unipotent i ν))
    (fun s => isSemidirectDecomposition_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν (Finset.univ \ s))
    (fun s => canonicalStandardUnipotent_isClosed hG i ν hi hν (Finset.univ \ s))
    (fun s => standardUnipotent_isUnimodular i ν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν standardCocharacter hG hi hν) (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone
      (standardParabolic_monotone i ν standardParabolicOrder hG hi hν))
    (StandardComplex.removedFamily_monotone
      (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)) E q

/-- The canonical projection onto the incoming-image quotient at any degree. -/
abbrev canonicalRationalTerminalProjection :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    type_of% (rationalTerminalProjection i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalTerminalProjection i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q

/-- The retained terminal cokernel at removed-root degree `|S| - |I|`. -/
abbrev canonicalRationalSharpObject :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (I : Finset (SimpleRoot i ν)),
    type_of% (rationalSharpObject i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E I) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E I =>
  rationalSharpObject i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E I

/-- The same retained terminal cokernel functor on the full smooth category. -/
abbrev canonicalRationalSharpFunctor :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν)),
    type_of% (rationalSharpFunctor.{u, v} i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) I) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun I =>
  rationalSharpFunctor.{u, v} i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) I

/-- The actual augmentation into degree zero. -/
abbrev canonicalRationalInitialMap :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
    type_of% (rationalInitialMap i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E =>
  rationalInitialMap i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E

/-- The full-root endpoints identify the actual input with degree zero. -/
abbrev canonicalRationalInitialEquiv :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
    type_of% (rationalInitialEquiv i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) standardParabolicEndpoints E) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E =>
  rationalInitialEquiv i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) standardParabolicEndpoints E

/-- The first arrow from the input smooth representation. -/
abbrev canonicalRationalInitialDifferential :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
    type_of% (rationalInitialDifferential i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E =>
  rationalInitialDifferential i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E

include hG i ν hi hν in
/-- The chosen exterior signs give square zero for the actual differentials. -/
theorem canonicalRationalDifferential_square :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    (canonicalRationalDifferential hG i ν hi hν E (q + 1)).comp
      (canonicalRationalDifferential hG i ν hi hν E q) = 0 :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  Complex.differential_square.{u, u, max (u + 1) v} _ _ _ _ _ _ _ _ E q

include hG i ν hi hν in
/-- The next differential kills the actual first arrow from the input. -/
theorem canonicalRationalInitialDifferential_square :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
    (canonicalRationalDifferential hG i ν hi hν E 1).comp
      (canonicalRationalInitialDifferential hG i ν hi hν E) = 0 :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E =>
  Complex.initialDifferential_square.{u, u, max (u + 1) v} _ _ _ _ _ _ _ _ E

include hG i ν hi hν in
/-- The retained quotient projection is onto, with no length premise. -/
theorem canonicalRationalTerminalProjection_surjective :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    Function.Surjective (canonicalRationalTerminalProjection hG i ν hi hν E q) :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalTerminalProjection_surjective i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q

include hG i ν hi hν in
/-- The final kernel is the actual incoming image. -/
theorem canonicalRationalTerminalProjection_ker :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    LinearMap.ker (canonicalRationalTerminalProjection hG i ν hi hν E q).toLinearMap =
      canonicalRationalBoundary hG i ν hi hν E q :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  rationalTerminalProjection_ker i ν standardCocharacter standardParabolicOrder hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) E q

include hG i ν hi hν in
/-- The retained quotient kills its incoming differential. -/
theorem canonicalRationalTerminalProjection_comp_differential :
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  ∀ [LinearOrder (SimpleRoot i ν)] (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ),
    (canonicalRationalTerminalProjection hG i ν hi hν E (q + 1)).comp
      (canonicalRationalDifferential hG i ν hi hν E q) = 0 :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI := hi.isSplitSubtorus.mono
  letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
    hi.isSplitSubtorus.1 ν
  fun E q =>
  Complex.terminalProjection_comp_differential.{u, u, max (u + 1) v}
    _ _ _ _ _ _ _ _ E q

end Langlands.Aubert.General.RationalPointFamily
