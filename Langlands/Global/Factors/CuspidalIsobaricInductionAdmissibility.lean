import Langlands.Global.AdelicOperatorTensorJointAdmissibility
import Langlands.Global.Factors.CuspidalInducedFiniteAdmissibility
import Langlands.Global.Factors.CuspidalIsobaricInducedTensor
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible

/-! # Joint admissibility of the original-order cuspidal induction tensor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 90000

universe u uQ

namespace Langlands.Global.CuspidalInducedFiniteTensor

open NumberField Langlands.Archimedean Langlands.Automorphic AdelicOperatorTensor
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open FiniteAdelicGL PrincipalSeries

private theorem compactOrbit_separates {L : Type} [RCLike L] {n : ℕ} {χ : ℕ → Lˣ → ℂ}
    {V : Submodule ℂ (GeneralLinear n L → ℂ)} (hV : V ≤ principalSeries L n χ)
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) L) (kFiniteFunctions V (unitaryCompact L n)))
    (hκ : ∀ k f, (κ k f : GeneralLinear n L → ℂ) =
      Whittaker.rightTranslation ℂ (GeneralLinear n L) (Unitary.toUnits k) f)
    (f : kFiniteFunctions V (unitaryCompact L n)) (hf : ∀ k, kFiniteEval V 1 (κ k f) = 0) :
    f = 0 := by
  apply Subtype.ext
  apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hV f.property.1)
  intro k hk
  let u : Matrix.unitaryGroup (Fin n) L := ⟨k.val, hk⟩
  have hku : Unitary.toUnits u = k := Units.ext rfl
  have h := hf u
  rw [kFiniteEval_apply, hκ, hku] at h
  change f.val (1 * k) = 0 at h
  rwa [one_mul] at h

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}
  (hm : ∑ i, (m i + 1) = r + 1)
  (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
  (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

local instance jointAdmissibilityTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
  {E : Finset (FinitePlace F)}
  (D : TensorSubquotient F (r + 1) (source hm P h) (fun v => (A v).obj.representation) E)

set_option quotPrecheck false in
local notation "RealBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten
set_option quotPrecheck false in
local notation "ComplexBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten

set_option maxHeartbeats 3000000 in
/-- The full source of the prescribed constituent has finite multiplicity
at each finite level and archimedean compact type. -/
theorem sourceTensor_isJointlyAdmissible
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :
    IsJointlyAdmissible
      (tensorFiniteAction F (r + 1)
        (Vr := fun v => realStandardKFinite (r + 1) RealBlocks(real, v))
        (Vc := fun v => complexStandardKFinite (r + 1) ComplexBlocks(complex, v))
        (sourceFiniteAction hm P h E D.sourceReference D.source_fixed))
      (tensorCompactAction F (r + 1)
        (fun v => realStandardRep (r + 1) RealBlocks(real, v))
        (fun v => complexStandardRep (r + 1) ComplexBlocks(complex, v))) := by
  refine tensor_isJointlyAdmissible F (r + 1) _ _
    (fun v => kFiniteEval (realStandardModule (r + 1) RealBlocks(real, v)) 1)
    (fun v => kFiniteEval (complexStandardModule (r + 1) ComplexBlocks(complex, v)) 1)
    (sourceFiniteAction hm P h E D.sourceReference D.source_fixed)
    (sourceTensor_isAdmissible hm P h E D.sourceReference D.source_fixed D.source_nonzero) ?_ ?_
  · intro v
    exact compactOrbit_separates (realStandardModule_le_principalSeries (r + 1) RealBlocks(real, v))
      (realStandardRep (r + 1) RealBlocks(real, v)) (realStandardRep_apply_coe (r + 1) RealBlocks(real, v))
  · intro v
    exact compactOrbit_separates le_rfl (complexStandardRep (r + 1) ComplexBlocks(complex, v))
      (principalSeriesRep_apply_coe ℂ (r + 1) _)

end Langlands.Global.CuspidalInducedFiniteTensor
