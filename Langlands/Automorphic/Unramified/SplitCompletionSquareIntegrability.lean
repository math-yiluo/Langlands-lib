import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Galois.QuadraticPatchingStatement
import Langlands.Global.Arithmetic.CMHalfWeightLocalNormControl
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Mathlib.LinearAlgebra.Trace

/-! # Square-integrability under split completion comparison -/

noncomputable section

open Langlands.Global
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe uF uE

namespace Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

/-- At a completely split place, the actual completion map is a field isomorphism. -/
def splitCompletionEquiv (v : FinitePlace F) (w : FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal] (hs : SplitsCompletelyAt (N := E) v) :
    FiniteCompletion F v ≃+* FiniteCompletion E w :=
  RingEquiv.ofBijective (completionMap v w)
    (Module.Free.bijective_algebraMap_of_finrank_eq_one (hs w inferInstance))

/-- The split completion isomorphism is a homeomorphism for the completion topologies. -/
def splitCompletionHomeomorph (v : FinitePlace F) (w : FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal] (hs : SplitsCompletelyAt (N := E) v) :
    FiniteCompletion F v ≃ₜ FiniteCompletion E w :=
  (splitCompletionEquiv v w hs).toEquiv.toHomeomorphOfIsInducing
    (CMHalfWeight.isEmbedding_completionMap v w).isInducing

end Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Automorphic.LocalRealization

open Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K : Type*} [Field K] [NumberField K]

local instance splitSquareRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance splitSquareContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance splitSquareSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance splitSquareFormsAddCommGroup (n : ℕ) : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance splitSquareLocalAddCommGroup {n : ℕ} {v : FinitePlace K}
    (L : LocalRealization K n v) :
    AddCommGroup L.Space :=
  Submodule.addCommGroup _

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

set_option maxHeartbeats 500000 in
/-- A representation equivalence over the actual split completion map
transports square-integrability to the upper local realization. -/
theorem isSquareIntegrable_of_splitCompletion_equiv {r : ℕ}
    {v : FinitePlace F} {w : FinitePlace E} [w.asIdeal.LiesOver v.asIdeal]
    (hs : SplitsCompletelyAt (N := E) v)
    {L : LocalRealization F (r + 1) v} {M : LocalRealization E (r + 1) w}
    (e : L.representation.Equiv
      (M.representation.comp (Matrix.GeneralLinearGroup.map (completionMap v w))))
    (hL : L.IsSquareIntegrable) : M.IsSquareIntegrable := by
  let base := (CompletionPadic.padicField v).canonicalTopologicalData
  let upper := (CompletionPadic.padicField w).canonicalTopologicalData
  let σ := splitCompletionEquiv v w hs
  let h := splitCompletionHomeomorph v w hs
  have hσ : @Continuous (FiniteCompletion F v) (FiniteCompletion E w)
      base.topology upper.topology σ := by
    rw [← CompletionPadic.completion_topology_eq v, ← CompletionPadic.completion_topology_eq w]
    exact h.continuous
  have hσs : @Continuous (FiniteCompletion E w) (FiniteCompletion F v)
      upper.topology base.topology σ.symm := by
    rw [← CompletionPadic.completion_topology_eq v, ← CompletionPadic.completion_topology_eq w]
    exact h.symm.continuous
  let := base.topology
  let := upper.topology
  let φ := GeneralLinear.fieldEquiv (r + 1) σ hσ hσs
  change L.representation.Equiv (M.representation.comp φ.toMonoidHom) at e
  refine ⟨(isIrreducible_comp_continuousMulEquiv_iff M.representation φ).mp
    ((isIrreducible_iff_of_equiv e).mp hL.1), ?_⟩
  have hPullback := (base.isSquareIntegrable_iff_of_equiv e).mp hL.2
  let := base.generalLinearTopologicalGroup (r + 1)
  let := upper.generalLinearTopologicalGroup (r + 1)
  let := base.centralQuotientMeasurableSpace (r + 1)
  let := upper.centralQuotientMeasurableSpace (r + 1)
  let := base.centralQuotientBorelSpace (r + 1)
  let := upper.centralQuotientBorelSpace (r + 1)
  intro μ hμ
  have hSquare := isSquareIntegrableModCenter_comp_continuousMulEquiv
    (M.representation.comp φ.toMonoidHom) φ.symm μ
    (hPullback (μ.map (centralQuotientCongr φ.symm)))
  have hAction :
      (M.representation.comp φ.toMonoidHom).comp φ.symm.toMonoidHom = M.representation := by
    apply MonoidHom.ext
    intro g
    exact congrArg M.representation (φ.apply_symm_apply g)
  rwa [hAction] at hSquare

end Langlands.Automorphic.LocalRealization
