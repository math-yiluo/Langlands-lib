import Langlands.ClassFieldTheory.Local.DivisionEmbeddingFromSplitting
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedDegree
import Langlands.ClassFieldTheory.Local.LocalDivisionArithmeticUniformizer

/-! # The actual unramified subfield and division uniformizer in Drinfeld's presentation -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralSimple CentralDivision
open _root_.Langlands.Brauer Langlands.ClassFieldTheory.Local Langlands.LocalField
open Langlands.LocalGalois.Separable

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D]

local notation "d" => CentralSimple.reducedDegree K D

/-- The selected arithmetic-unramified stage of degree equal to the reduced degree. -/
abbrev drinfeldUnramifiedField : IntermediateField K (SeparableClosure K) :=
  finiteUnramifiedFieldOfDegree K d (reducedDegree_pos K D)

/-- The selected field is arithmetic-unramified for the original valuation. -/
theorem drinfeldUnramifiedField_unramified :
    ArithmeticUnramified K (drinfeldUnramifiedField K D) :=
  finiteUnramifiedFieldOfDegree_unramified K d (reducedDegree_pos K D)

/-- The selected field has the exact reduced degree. -/
theorem drinfeldUnramifiedField_degree : Module.finrank K (drinfeldUnramifiedField K D) = d :=
  finiteUnramifiedFieldOfDegree_finrank K d (reducedDegree_pos K D)

variable [Algebra.IsCentral K D]
  (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
    reciprocalClass (CentralSimple.reducedDegree K D))

include hInv in
private theorem drinfeldUnramifiedField_splits :
    IsSplit (baseChange (drinfeldUnramifiedField K D) (divisionAlgebraCSA K D)) := by
  let E := drinfeldUnramifiedField K D
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  have h := hInv
  rw [classOf_opposite, map_neg] at h
  have hInvD : localBrauerInvariant K (classOf (divisionAlgebraCSA K D)) = -reciprocalClass d :=
    neg_eq_iff_eq_neg.mp h
  have hd : d • reciprocalClass d = 0 := by
    rw [← denominatorEquiv_one d (reducedDegree_pos K D)]
    exact (denominatorEquiv d (reducedDegree_pos K D) 1).property
  apply (localBrauerInvariant_eq_zero_iff E _).mp
  rw [← scalarExtension_classOf,
    localBrauerInvariant_scalarExtension K E (spectralFiniteExtension_algebraMap_continuous K E),
    hInvD, drinfeldUnramifiedField_degree K D, smul_neg, hd, neg_zero]

/-- Embed the selected degree-d unramified field in the original division algebra. -/
def drinfeldUnramifiedEmbedding : drinfeldUnramifiedField K D →ₐ[K] D :=
  embeddingOfSplitOfReducedDegree K D (drinfeldUnramifiedField K D)
    (drinfeldUnramifiedField_degree K D) (drinfeldUnramifiedField_splits K D hInv)

variable {π : 𝒪[K]} (hπ : Irreducible π)

/-- The division uniformizer with the prescribed scalar power for the chosen
unramified embedding. -/
def drinfeldArithmeticUniformizer : Dˣ :=
  arithmeticDivisionUniformizer K D (drinfeldUnramifiedField K D)
    (drinfeldUnramifiedField_unramified K D) (drinfeldUnramifiedEmbedding K D hInv)
    (drinfeldUnramifiedField_degree K D) hπ hInv

@[simp]
theorem drinfeldArithmeticUniformizer_pow :
    (drinfeldArithmeticUniformizer K D hInv hπ : D) ^ d = algebraMap K D (π : K) :=
  arithmeticDivisionUniformizer_pow K D _ _ _ _ hπ _

/-- The original division action conjugates the embedded field by its arithmetic Frobenius. -/
theorem drinfeldArithmeticUniformizer_mul (x : drinfeldUnramifiedField K D) :
    (drinfeldArithmeticUniformizer K D hInv hπ : D) * drinfeldUnramifiedEmbedding K D hInv x =
      drinfeldUnramifiedEmbedding K D hInv
        (finiteUnramifiedFrobenius K (drinfeldUnramifiedField K D)
          (drinfeldUnramifiedField_unramified K D) x) * (drinfeldArithmeticUniformizer K D hInv hπ : D) :=
  arithmeticDivisionUniformizer_mul K D _ _ _ _ hπ _ x

end Langlands.FormalGroup.LocalDivision
