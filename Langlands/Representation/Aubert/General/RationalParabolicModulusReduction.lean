import Langlands.Representation.Aubert.General.RationalParabolicModulusStatement
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Aubert.General.RationalLeviRegularity
import Langlands.Representation.Aubert.General.SemidirectModularCharacter

/-! # The actual parabolic comparison from intrinsic Levi unimodularity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open MeasureTheory.Measure

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalParabolicModulusPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- The standard parabolic modulus formula follows from intrinsic
unimodularity of its literal Levi. All topological inputs are derived from
the premises of the exact rational-parabolic target. -/
theorem standardParabolic_modularCharacter_of_levi
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (hπ : Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (hM :
      haveI : LocallyCompactSpace (levi i ν I) :=
        ((isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).isClosed_levi_of_continuous_projection
            hP hπ).locallyCompactSpace
      ∀ m : levi i ν I, modularCharacter m = 1) :
    haveI : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
    ∀ p : parabolic i ν I, modularCharacter p =
      (HaarModulus.closedRestrictCharacter (unipotent i ν I) hU (parabolic i ν I)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).le_normalizer p : ℝ≥0) := by
  let h := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I
  have : SecondCountableTopology (RationalPoint k G.X) :=
    reductiveRationalPoint_secondCountable k G hG
  have : LocallyCompactSpace (levi i ν I) :=
    (h.isClosed_levi_of_continuous_projection hP hπ).locallyCompactSpace
  have : LocallyCompactSpace (unipotent i ν I) := hU.locallyCompactSpace
  have : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
  have hδU := standardUnipotent_isUnimodular_of_standardCocharacterStatement
    i ν hStandard hG hi hν I hU
  intro p
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    h.modularCharacter_eq_restrictCharacter_of_unimodular hπ hM hδU p

end Langlands.Aubert.General.RationalPointFamily
