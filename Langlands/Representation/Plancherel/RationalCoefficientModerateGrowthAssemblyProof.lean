import Langlands.Representation.Plancherel.RationalCoefficientModerateGrowthAssemblyStatement
import Langlands.Representation.Plancherel.RationalFiniteSignedCartanCoverProof
import Langlands.Representation.Plancherel.RationalFiniteChartModerateGrowthProof

/-! # Assembling coefficient growth from one joint geometric witness -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open GroupScheme BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

/-- The two structural targets supply all witnesses needed for the global
coefficient bound, without further premises on the representation. -/
theorem rationalCoefficientModerateGrowthAssembly :
    RationalCoefficientModerateGrowthAssemblyStatement.{u, uV} := by
  intro hStandard hJoint F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  classical
  obtain ⟨S, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  let : Fintype (SimpleRoot i ν) :=
    simpleRelativeRootFintypeOfIsSplitTorus i hi.isSplitSubtorus.1 ν
  obtain ⟨D, x, Z, j, s, -, -, hsj, h, -, hprops, -, -, -, -, hcompat, hBasis⟩ :=
    hJoint F G hG S i hi ν hν
  obtain ⟨F₀, hF₀⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  obtain ⟨k, gen, hgen, hnonneg, T, hT, hcover⟩ :=
    rationalFiniteSignedCartanCover F G hG S i hi ν hν hStandard
      D x Z j s h hsj hcompat F₀ hF₀
  exact rationalFiniteChartModerateGrowth
    F G hG S i hi ν (D.specialCompactSubgroup x) hBasis
    (Fin k → Bool) (SimpleRoot i ν ⊕ Fin k) gen hgen hnonneg
    (D.specialCompactSubgroup x) (D.specialCompactSubgroup x) T
    hprops.2.1.1 hprops.2.1.1 hT hcover

end Langlands.Plancherel
