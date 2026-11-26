import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Global.AdelicBlockAnchorInjectivity
import Langlands.Global.AdelicEisensteinGenericInjectivityProof
import Langlands.Global.Factors.CuspidalBlockInductionReferences
import Langlands.Global.Factors.CuspidalIsobaricBlockSpecialization
import Langlands.Global.Factors.CuspidalIsobaricFiniteFamily
import Langlands.Representation.Archimedean.RealGenericStandardParameterProof
import Langlands.Representation.Archimedean.RealTemperedIrreducibleProof

/-! # All-places isobaric automorphy from the actual block section model -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global

open Automorphic _root_.Langlands.Archimedean NumberField
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CuspidalBlockInduction (blockShape)
open AdelicBlockScalarSections (blockEisensteinInjectivityReduction)

local instance blockSectionTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The original-order restricted tensor of local inductions embeds into the
actual smooth scalar sections of the standard cuspidal block parabolic. -/
def CuspidalIsobaricBlockSectionEmbeddingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (E : Finset (FinitePlace F))
    (hsub : ∀ v, IsSubquotientOf (CuspidalInducedFiniteTensor.source hm P h v) (A v).obj.representation)
    (hfixed : ∀ v ∉ E, fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥)
    (real : ∀ v : {v : InfinitePlace F // InfinitePlace.IsReal v}, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : {v : InfinitePlace F // InfinitePlace.IsComplex v}, ComplexIsobaricPlaceData (r := r) T v),
    CuspidalInducedFiniteTensor.HasBlockSectionEmbedding (blockShape hm)
      (fun i => (T i).realization) A (CuspidalInducedFiniteTensor.assemble hm P h A E hsub hfixed)
      real complex

/-- The block induction comparison and Eisenstein continuation realize the
prescribed tensor as a quotient of a space of actual automorphic forms. -/
theorem cuspidalIsobaricTensorRealization_of_blockSections
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hcomparison : CuspidalIsobaricBlockSectionEmbeddingStatement.{u, uQ}) :
    CuspidalIsobaricTensorRealizationStatement.{u, uQ} := by
  intro F _ _ _ r k m hm T P h A E hsub hfixed real complex
  have hS (i : Fin k) : (T i).realization.IsJointlyAdmissible := (T i).isJointlyAdmissible
  have hInjective := blockEisensteinInjectivityReduction hcont eisensteinGenericInjectivity F r
    (blockShape hm) (fun i => (T i).realization) hS
  exact CuspidalInducedFiniteTensor.hasTensorRealization_of_blockSectionEmbedding
    (blockShape hm) (fun i => (T i).realization) A
    (CuspidalInducedFiniteTensor.assemble hm P h A E hsub hfixed) real complex
    hS hcont hInjective (hcomparison F r k m hm T P h A E hsub hfixed real complex)

/-- The all-places isobaric automorphy conclusion from the induction model and
Eisenstein continuation. The finite and archimedean local inputs are proved. -/
theorem cuspidalIsobaricAutomorphy_of_blockSections
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hcomparison : CuspidalIsobaricBlockSectionEmbeddingStatement.{u, uQ}) :
    CuspidalIsobaricAutomorphyStatement.{u, uQ} :=
  cuspidalIsobaricAutomorphy_of_tensorRealization realGenericStandardParameter
    realTemperedStandardIrreducible cuspidalIsobaricFiniteFamily
    (cuspidalIsobaricTensorRealization_of_blockSections hcont hcomparison)

end Langlands.Global
