import Langlands.Representation.Aubert.General.CanonicalRationalComplex
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof

/-! # The full-support endpoint of the actual smooth Aubert complex -/

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

/-- At full support the actual terminal cokernel functor is naturally the identity. -/
def canonicalRationalSharpUnivIso :
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
  ∀ [LinearOrder (SimpleRoot i ν)],
    canonicalRationalSharpFunctor.{u, v} hG i ν hi hν Finset.univ ≅ 𝟭 (SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :=
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
  by
    apply Complex.terminalIsoOfDegreeEqZero.{u, u, max (u + 1) v}
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
        (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν))
    · change parabolic i ν (Finset.univ \ ∅) = ⊤
      rw [Finset.sdiff_empty]
      exact standardParabolic_univ i ν standardParabolicEndpoints hG hi hν
    · change unipotent i ν (Finset.univ \ ∅) = ⊥
      rw [Finset.sdiff_empty]
      exact standardUnipotent_univ i ν standardParabolicEndpoints hG hi hν
    · exact Nat.sub_self _

include hG i ν hi hν in
/-- The degree-zero terminal projection divides out no vectors. -/
theorem canonicalRationalTerminalProjection_zero_injective :
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
    Function.Injective (canonicalRationalTerminalProjection hG i ν hi hν E 0) :=
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
  Complex.terminalProjection_zero_injective.{u, u, max (u + 1) v} _ _ _ _ _ _ _ _ E

include hG i ν hi hν in
/-- The actual initial map followed by the degree-zero quotient is bijective. -/
theorem canonicalRationalInitialTerminalMap_bijective :
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
    Function.Bijective ((canonicalRationalTerminalProjection hG i ν hi hν E 0).comp
      (canonicalRationalInitialMap hG i ν hi hν E)) :=
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
  by
    apply Complex.initialTerminalMap_bijective.{u, u, max (u + 1) v}
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
        (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν))
    · change parabolic i ν (Finset.univ \ ∅) = ⊤
      rw [Finset.sdiff_empty]
      exact standardParabolic_univ i ν standardParabolicEndpoints hG hi hν
    · change unipotent i ν (Finset.univ \ ∅) = ⊥
      rw [Finset.sdiff_empty]
      exact standardUnipotent_univ i ν standardParabolicEndpoints hG hi hν

end Langlands.Aubert.General.RationalPointFamily
