import Langlands.BaseChange.TwistedCharacterRegularValuesStatement
import Langlands.BaseChange.TwistedCharacter.OperatorLocalConstancy
import Langlands.BaseChange.TwistedCharacter.Smearing
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-! # Reduction of twisted character regularity to compact pushforward geometry -/

namespace Langlands.BaseChange

open MeasureTheory

section Topology

universe u v

/-- An algebra automorphism of an algebra with its module topology acts continuously on
the general linear group by applying the automorphism to each entry. -/
theorem continuous_entrywiseAut_of_isModuleTopology {F : Type u} [CommRing F] [TopologicalSpace F]
    {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (n : ℕ) : Continuous (entrywiseAut σ n) := by
  have : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ.toLinearMap
  let f : Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) E :=
    RingHom.mapMatrix (σ : E →+* E)
  have hf : Continuous f := continuous_matrix fun i j => hσ.comp (continuous_apply_apply i j)
  exact hf.units_map f.toMonoidHom

/-- `GL_n(E)` is second countable when `E` is a finite algebra over a nonarchimedean
local field and has its module topology. -/
theorem generalLinear_secondCountableTopology_of_finite
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E]
    [TopologicalSpace E] [IsModuleTopology F E] (n : ℕ) :
    SecondCountableTopology (GeneralLinear n E) := by
  have := HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  have := (finiteCoordinateHomeomorph F E).isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) E)).symm.isEmbedding
      |>.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end Topology

/-- The geometric input for compact averaging at σ-regular elements of `GL_n(E)` over
a cyclic algebra. The compact subgroup and the representatives give a Cartan covering,
the representatives uniformly contract suitable compact open subgroups of `P`, and the
normalized compact twisted conjugation pushforwards are locally constant. -/
def TwistedCharacterRegularValuesGeometryStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    IsCyclicAlgebra σ l →
    ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ →
      ∃ (K P : Subgroup (GeneralLinear n E)) (hK : IsCompact (K : Set (GeneralLinear n E)))
        (M : Set (GeneralLinear n E)),
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
        HasCartanCoverage K M ∧ HasUniformCartanContraction P M ∧
          HasLocallyConstantTwistedConjugationPushforward (entrywiseAut σ n) K P δ

/-- The compact averaging geometry implies the Library's twisted character regularity
statement, in all three universes of the target. -/
def TwistedCharacterRegularValuesReductionStatement.{u, v, uW} : Prop :=
  TwistedCharacterRegularValuesGeometryStatement.{u, v} →
    TwistedCharacterRegularValuesStatement.{u, v, uW}

/-- The generic local constancy and smearing theorems apply with the continuous entrywise
automorphism and the representation's intertwining isomorphism. -/
theorem twistedCharacterRegularValuesReduction.{u, v, uW} :
    TwistedCharacterRegularValuesReductionStatement.{u, v, uW} := by
  intro hGeom F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  have := generalLinear_secondCountableTopology_of_finite F E n
  intro W _ _ τ hτ hirr A δ hδ
  obtain ⟨K, P, hK, M, hCartan, hContract, hPush⟩ := hGeom F E σ l n hE δ hδ
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  exact exists_hasTwistedCharacterValue_of_eventuallyEq τ K hτ A.toLinearMap δ
    (conjugationAverage_eventuallyEq_of_pushforward (entrywiseAut σ n) K τ hτ.1 A.toLinearMap
      (continuous_entrywiseAut_of_isModuleTopology σ n) A.comp_apply_eq hirr M hCartan hContract δ hPush)

end Langlands.BaseChange
