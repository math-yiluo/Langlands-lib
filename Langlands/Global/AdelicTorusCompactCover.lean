import Langlands.Global.AdelicGaloisUnitQuotient
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Compact principal representatives for arbitrary actual number-field tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (T : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom]

/-- Every actual number-field torus has compact representatives in its full norm-one group. -/
theorem hasCompactNormOneRationalCover_of_isTorus (hT : IsTorus T) :
    HasCompactNormOneRationalCover T := by
  obtain ⟨L, hL, hFL, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting F T hT
  let : Field L := hL
  let : Algebra F L := hFL
  let : FiniteDimensional F L := hfin
  let : IsGalois F L := hgal
  let : NumberField L := NumberField.of_module_finite F L
  apply AdelicGaloisUnit.hasCompactNormOneRationalCover_of_baseChange F L T
  exact hasCompactNormOneRationalCover_of_isSplitTorus L _ hsplit

/-- A compact set of principal representatives for the actual norm-one points of a torus. -/
def torusCompactSet (hT : IsTorus T) : Set (normOneSubgroup F T) :=
  (hasCompactNormOneRationalCover_of_isTorus F T hT).choose

/-- The constructed representative set is compact in the original subgroup topology. -/
theorem isCompact_torusCompactSet (hT : IsTorus T) : IsCompact (torusCompactSet F T hT) :=
  (hasCompactNormOneRationalCover_of_isTorus F T hT).choose_spec.1

/-- Every norm-one point has an actual principal translate in the constructed set. -/
theorem exists_rational_mul_mem_torusCompactSet (hT : IsTorus T)
    (g : normOneSubgroup F T) :
    ∃ q : RationalGroupPoints F T, rationalNormOne F T q * g ∈ torusCompactSet F T hT :=
  (hasCompactNormOneRationalCover_of_isTorus F T hT).choose_spec.2 g

end Langlands.Global.AdelicGroupPoints
