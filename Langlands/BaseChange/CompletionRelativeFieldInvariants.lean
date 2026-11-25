import Langlands.Global.FiniteAdelicGL.BlockInductionNormalization
import Langlands.BaseChange.DifferentExponentExistence
import Langlands.BaseChange.StandardAdelicTraceCharacter
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilTransferReduction
import Langlands.Global.CompletionResidueAdic
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.LocalField.SuppliedPadicExtension
import Mathlib.FieldTheory.Galois.Abelian

/-! # The actual field invariants at an auxiliary finite completion -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.BaseChange

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel
open Global Global.AdelicFunctoriality Global.CompletionPadic
open Automorphic.CuspidalWhittaker Global.HeckeFunctionalEquation ClassFieldTheory.Global.FundamentalClass
open scoped NumberField FiniteExtension

section Cardinality

variable {K : Type u} [Field K] [NumberField K]

private theorem completion_residueCardinalityAt_eq_absNorm (w : Global.FinitePlace K)
    {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (padicFieldAt w h).canonicalTopologicalData.residueCardinality = Ideal.absNorm w.asIdeal := by
  subst p
  exact Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm w

end Cardinality

section Relative

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : Global.FinitePlace K) (w : Global.FinitePlace L) [w.asIdeal.LiesOver v.asIdeal]

local notation "Kv" => v.adicCompletion K
local notation "Lw" => w.adicCompletion L
local notation "TF" => PadicField.canonicalTopologicalData (padicField v)
local notation "TE" => PadicField.canonicalTopologicalData (CompletionPadic.towerPadicField v w)

/-- Completion of a cyclic extension is cyclic, using the decomposition map. -/
theorem completion_isAbelianGalois [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    IsAbelianGalois Kv Lw := by
  let := isGalois_adicCompletion v w
  let := isCyclic_of_injective (decompositionHom v w)
    (ClassFieldTheory.Global.decompositionHom_injective v w)
  exact IsAbelianGalois.of_isCyclic Kv Lw

/-- The completed residue degree is the inertia degree of the upper prime. -/
theorem completion_isResidueDegree :
    letI := (TF).valuativeRel
    letI := (TE).valuativeRel
    IsResidueDegree Kv Lw (w.asIdeal.inertiaDeg (𝓞 K)) := by
  let := (TF).valuativeRel
  let := (TE).valuativeRel
  change (TE).residueCardinality = (TF).residueCardinality ^ _
  rw [completion_residueCardinalityAt_eq_absNorm w (residuePrime_eq v w),
    Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm v]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

/-- The standard additive character at an upper completion is obtained by the local trace. -/
theorem standardFiniteAdditiveComponent_trace (x : Lw) :
    standardFiniteAdditiveComponent L w x =
      standardFiniteAdditiveComponent K v (Algebra.trace Kv Lw x) := by
  classical
  rw [isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent L w,
    isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v,
    ← standardAdelicTraceCharacter K L]
  exact traceAdditiveCharacter_single (standardGlobalAdditiveCharacter K)
    (standardGlobalAdditiveCharacter_diagonal K) v ⟨w, inferInstance⟩ x

private theorem isModuleTopology_completion_topology : IsModuleTopology Kv Lw := by
  let : NontriviallyNormedField Kv := Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

end Relative

/-- At a finite completion of a cyclic number-field extension, the canonical p-adic
packages have the actual relative module topology and the stated residue degree.
The relative trace codifferent has a natural exponent. -/
def CompletionRelativeFieldInvariantsStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (v : Global.FinitePlace K) (w : Global.FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal],
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (CompletionPadic.towerPadicField v w).canonicalTopologicalData.topology
    letI := (padicField v).canonicalTopologicalData.valuativeRel
    letI := (CompletionPadic.towerPadicField v w).canonicalTopologicalData.valuativeRel
    IsModuleTopology (v.adicCompletion K) (w.adicCompletion L) ∧
      IsAbelianGalois (v.adicCompletion K) (w.adicCompletion L) ∧
      IsResidueDegree (v.adicCompletion K) (w.adicCompletion L) (w.asIdeal.inertiaDeg (𝓞 K)) ∧
      ∃ d, IsDifferentExponent (v.adicCompletion K) (w.adicCompletion L) d

set_option maxHeartbeats 900000 in
/-- Use the published completion structure and compute the trace codifferent locally. -/
theorem completionRelativeFieldInvariants : CompletionRelativeFieldInvariantsStatement.{u} := by
  intro K L _ _ _ _ _ _ _ v w _
  let F := padicField v
  let E := CompletionPadic.towerPadicField v w
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TE.topology
  let := TF.valuativeRel
  let := TE.valuativeRel
  let := TF.localField
  let := TE.localField
  let := completion_isAbelianGalois v w
  have hcont : Continuous (algebraMap F.Carrier E.Carrier) := by
    change @Continuous _ _ TF.topology TE.topology (FiniteExtension.completionMap v w)
    rw [← completion_topology_eq v, ← padicFieldAt_topology_eq w (residuePrime_eq v w)]
    exact FiniteExtension.continuous_completionMap v w
  have htop : IsModuleTopology F.Carrier E.Carrier := by
    change @IsModuleTopology _ TF.topology _ _ _ TE.topology
    rw [← completion_topology_eq v, ← padicFieldAt_topology_eq w (residuePrime_eq v w)]
    exact isModuleTopology_completion_topology v w
  let := Langlands.LocalField.valuativeExtension_of_continuous hcont
  exact ⟨htop, inferInstance, completion_isResidueDegree v w,
    differentExponentExistence F.Carrier E.Carrier hcont⟩

end Langlands.BaseChange
