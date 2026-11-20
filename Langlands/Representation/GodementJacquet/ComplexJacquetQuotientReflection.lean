import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement

/-! # The Whittaker reflection on the complex left-unipotent quotient -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.QuotientIntegration Langlands.RankinSelberg
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.Global.RankinSelbergGlobal
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "G" => GeneralLinear (r + 1) ℂ
local notation "U" => upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ

/-- The Whittaker reflection preserves the supplied compatible complex
quotient measure. -/
theorem measurePreserving_complexReflectionQuotient (D : ComplexQuotientMeasureData r) :
    MeasurePreserving (reflectionQuotient (K := ℂ) r) D.measure D.measure := by
  let : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
  let : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℂ))
  let hG := isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let : SecondCountableTopology G := hG.isInducing.secondCountableTopology
  have hclosed : IsClosed (U : Set G) := UpperUnipotent.isClosed
  let : LocallyCompactSpace U := hclosed.locallyCompactSpace
  let : SecondCountableTopology U := IsInducing.subtypeVal.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let e := reflectionAut (K := ℂ) r
  let eU := subgroupAutomorphism U e (reflectionAut_mem_iff r)
  let eQ := quotientAutomorphism U e (reflectionAut_mem_iff r)
  have hscale := D.compatible.map_quotientAutomorphism U hclosed e (reflectionAut_mem_iff r)
  have hg : mulEquivHaarChar e = 1 :=
    mulEquivHaarChar_eq_one_of_involutive e (reflectionAut_involutive r)
  have hu : mulEquivHaarChar eU = 1 :=
    mulEquivHaarChar_eq_one_of_involutive eU
      (fun u => Subtype.ext (reflectionAut_involutive r u.val))
  have hm : MeasurePreserving eQ D.measure D.measure := by
    refine ⟨eQ.continuous.measurable, ?_⟩
    change D.measure.map eQ =
      (((mulEquivHaarChar eU / mulEquivHaarChar e : ℝ≥0) : ℝ≥0∞)) • D.measure at hscale
    simpa only [hg, hu, div_one, ENNReal.coe_one, one_smul] using hscale
  exact (D.compatible.right_invariant (weylLong (r + 1) ℂ)).comp hm

end Langlands.GodementJacquet
