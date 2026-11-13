import Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements
import Langlands.Representation.Exponents.LeviJacquetContragredientDynamic
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Jacquet.CompressionSeparationBound
import Langlands.Representation.Jacquet.FixedVectorIrreducibleSeparation

/-! # Renard VI.9.1, bound and Remarks 1–2, from the uniform stabilization

The bound `b ≤ c(G, K)` and Remarks 1 and 2 of Renard 2026, VI.9.1 (PDF pp.203–204), follow
from the Proposition of VI.9.1 (`UniformCompressionStabilizationStatement`). This module states
the implication as a proposition and proves it. It does not prove the Proposition.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.9.1, the bound `b ≤ c(G, K)` and Remarks 1 and 2, from the Proposition of
VI.9.1. -/
theorem generalizedJacquetRemarks_of_uniformStabilization
    (hstab : UniformCompressionStabilizationStatement.{u, v}) :
    GeneralizedJacquetRemarksStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ χ K hK g N M Nbar hcent hI
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hN := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints (F := k) χ
  have hNbar := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints (F := k)
    (Dynamic.inverseCocharacter χ)
  have hMN := Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _))
  have hMNbar : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ≤
      Subgroup.normalizer (((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier
        (Over.mk (𝟙 _)) : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  have : SecondCountableTopology (rationalPoints G) :=
    reductiveRationalPoint_secondCountable k G hG
  have : DiscreteTopology (rationalPoints G ⧸ K.toSubgroup) :=
    QuotientGroup.discreteTopology K.isOpen
  have : Countable (rationalPoints G ⧸ K.toSubgroup) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨b, hb⟩ := hstab k G hG χ K hK g hcent hI
  refine ⟨fun c hc V _ _ ρ hρ => Jacquet.stabilization_bound_of_separation K hK g
      (Jacquet.fixedVectorsSeparatedByIrreducibles K hK) (fun W _ _ σ hσ => (hb W σ hσ).2) c hc ρ hρ, ?_⟩
  exact Jacquet.remarks_of_uniformStabilization hK hN hNbar hMN hMNbar
    (fun g' hc' hI' => hstab k G hG χ K hK g' hc' hI') hcent hI

/-- Renard VI.9.1: the Proposition (uniform stabilization of the compressed actions of
`M`-central Iwahori contractions) implies the bound `b ≤ c(G, K)` and Remarks 1 and 2. -/
def GeneralizedJacquetRemarksReductionStatement : Prop :=
  UniformCompressionStabilizationStatement.{u, v} → GeneralizedJacquetRemarksStatement.{u, v}

/-- The implication `GeneralizedJacquetRemarksReductionStatement`, at arbitrary universes. -/
theorem generalizedJacquetRemarksReduction : GeneralizedJacquetRemarksReductionStatement.{u, v} :=
  generalizedJacquetRemarks_of_uniformStabilization

end Langlands.Aubert.General.RationalPointFamily
