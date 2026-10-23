import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.Global.CompletionPadic
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.LocalField.Normalization.Proof

/-! # The canonical p-adic and completion models of a finite local GL factor -/

noncomputable section

namespace Langlands.Global.FiniteAdelicGL

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (v : FinitePlace K)

/-- The actual completion matrix topology equals the canonical p-adic matrix topology. -/
theorem localGL_topology_eq (n : ℕ) :
    inferInstanceAs (TopologicalSpace (FiniteLocalGL K n v)) =
      (CompletionPadic.padicField v).canonicalGeneralLinearTopology n := by
  unfold PadicField.canonicalGeneralLinearTopology
    PadicField.TopologicalData.generalLinearTopology
  rw [← CompletionPadic.completion_topology_eq v]
  rfl

/-- Completed integers and the canonical p-adic valuation ring have the same elements. -/
theorem mem_localIntegers_iff_canonical (x : FiniteCompletion K v) :
    x ∈ v.adicCompletionIntegers K ↔
      x ∈ (CompletionPadic.padicField v).canonicalTopologicalData.Integers :=
  (CompletionPadic.mem_adicCompletionIntegers_iff v x).trans
    ((CompletionPadic.padicField v).canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers x)

/-- The actual local integral subgroup is the canonical spherical subgroup. -/
theorem localIntegral_eq_sphericalSubgroup (r : ℕ) :
    (localIntegral K (r + 1) v).toSubgroup =
      Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r := by
  ext g
  change g ∈ localIntegral K (r + 1) v ↔
    g ∈ Conductor.integralSubgroup
      (CompletionPadic.padicField v).canonicalTopologicalData.Integers r
  rw [mem_localIntegral, Conductor.mem_integralSubgroup]
  simp only [mem_localIntegers_iff_canonical K v]

/-- Identity-supported local inclusion, with the canonical p-adic domain topology. -/
def localPadicInclusion (n : ℕ) :
    @ContinuousMonoidHom
      (GeneralLinear n (CompletionPadic.padicField v).Carrier) (FiniteAdelicGL K n) _ _
      ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n) _ := by
  let f : FiniteLocalGL K n v →* FiniteAdelicGL K n :=
    (localInclusion K n v).toMonoidHom
  have hf : Continuous f := (localInclusion K n v).continuous
  letI := (CompletionPadic.padicField v).canonicalGeneralLinearTopology n
  refine ⟨f, ?_⟩
  change @Continuous _ _ ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n) _ f
  rw [← localGL_topology_eq K v n]
  exact hf

@[simp] theorem localPadicInclusion_apply (n : ℕ)
    (g : GeneralLinear n (CompletionPadic.padicField v).Carrier) :
    localPadicInclusion K v n g = localInclusion K n v g := rfl

theorem localPadicInclusion_injective (n : ℕ) :
    Function.Injective (localPadicInclusion K v n) :=
  localInclusion_injective K n v

@[simp] theorem localProjection_localPadicInclusion (n : ℕ)
    (g : GeneralLinear n (CompletionPadic.padicField v).Carrier) :
    localProjection K n v (localPadicInclusion K v n g) = g :=
  localProjection_localInclusion K n v g

/-- The standard finite integral subgroup pulls back to the canonical spherical subgroup. -/
theorem comap_standardIntegral_localPadicInclusion (r : ℕ) :
    (standardIntegral K (r + 1)).toSubgroup.comap
      (@ContinuousMonoidHom.toMonoidHom
        (GeneralLinear (r + 1) (CompletionPadic.padicField v).Carrier)
        (FiniteAdelicGL K (r + 1)) _ _
        ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)) _
        (localPadicInclusion K v (r + 1))) =
        Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r := by
  change (standardIntegral K (r + 1)).toSubgroup.comap
    (localInclusion K (r + 1) v).toMonoidHom = _
  rw [comap_standardIntegral_localInclusion, localIntegral_eq_sphericalSubgroup]

end Langlands.Global.FiniteAdelicGL
