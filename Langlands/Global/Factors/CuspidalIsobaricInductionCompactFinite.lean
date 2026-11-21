import Langlands.Global.AdelicOperatorTensorCompactFinite
import Langlands.Global.Factors.CuspidalIsobaricInducedTensor

/-! # Compact finiteness of the original-order cuspidal induction tensor -/

noncomputable section

open scoped MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe u

namespace Langlands.Global.CuspidalInducedFiniteTensor

open NumberField Langlands.Archimedean Langlands.Automorphic AdelicOperatorTensor
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open FiniteAdelicGL

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

local instance compactFinitenessTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable {U : FinitePlace F → Type u} [∀ v, AddCommGroup (U v)] [∀ v, Module ℂ (U v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (U v)}
variable {E : Finset (FinitePlace F)}
variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
variable (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)

set_option quotPrecheck false in
local notation "RealBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten
set_option quotPrecheck false in
local notation "ComplexBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten

/-- The compact action on the same tensor as `sourceTensorAction`. -/
abbrev sourceCompactAction
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :=
  tensorCompactAction F (r + 1) (Vf := RestrictedTensor.Space ℂ U E D.sourceReference)
    (fun v => realStandardRep (r + 1) RealBlocks(real, v))
    (fun v => complexStandardRep (r + 1) ComplexBlocks(complex, v))

set_option maxHeartbeats 2300000 in
/-- Every vector in the original-order tensor is compact-finite, and its
compact action is semisimple over the group algebra. -/
theorem sourceCompactAction_finite_semisimple
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :
    let κ := sourceCompactAction A D real complex
    (∀ x, FiniteVectors.IsFiniteVector κ x) ∧
      IsSemisimpleModule ℂ[standardInfiniteCompact F (r + 1)] κ.asModule := by
  let κ := sourceCompactAction A D real complex
  have h (x : _) : FiniteVectors.IsFiniteVector κ x ∧
      ∀ ℓ : _ →ₗ[ℂ] ℂ, Continuous (fun k => ℓ (κ k x)) :=
    tensorCompactAction_finite_continuous F (r + 1) _ _
      (fun v => (isRealGKModule_realStandardModule (r + 1) RealBlocks(real, v)).1)
      (fun v => (isComplexGKModule_complexStandardModule (r + 1) ComplexBlocks(complex, v)).1)
      (fun v => (isRealGKModule_realStandardModule (r + 1) RealBlocks(real, v)).2.1)
      (fun v => (isComplexGKModule_complexStandardModule (r + 1) ComplexBlocks(complex, v)).2.1) x
  exact ⟨fun x => (h x).1, KFiniteDual.isSemisimpleModule (fun x => (h x).1) (fun x => (h x).2)⟩

end Langlands.Global.CuspidalInducedFiniteTensor
