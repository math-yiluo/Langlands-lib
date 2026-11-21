import Langlands.Global.Factors.CuspidalIsobaricInducedTensor

/-! # Simplicity and realization of the specified constituent tensor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator

universe u

namespace Langlands.Global.CuspidalInducedFiniteTensor

open Langlands.Archimedean Langlands.Automorphic AdelicOperatorTensor
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open FiniteAdelicGL

attribute [local instance 100] LieRing.ofAssociativeRing

section Irreducibility

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

private theorem irreducible_tensorFreeAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    {fin : Representation ℂ (FiniteAdelicGL F n) Vf}
    {κr : ∀ v : RP, Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (Vr v)}
    {δr : ∀ v : RP, (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {κc : ∀ v : CP, Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Vc v)}
    {δc : ∀ v : CP, (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    (hne : Nontrivial Vf)
    (hfin : ∀ (s : Finset Vf) (Y : Module.End ℂ Vf),
      ∃ X ∈ Algebra.adjoin ℂ (Set.range fin), ∀ x ∈ s, X x = Y x)
    (hr : ∀ v, GKModuleDensity.Hyp (κr v) (δr v))
    (hc : ∀ v, GKModuleDensity.Hyp (κc v) (δc v)) :
    Representation.IsIrreducible (tensorFreeAction F n fin κr δr κc δc).toMonoidHom :=
  isIrreducible_of_density (tensorFreeAction_hasActions F n fin κr δr κc δc) hne hfin hr hc

end Irreducibility

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance isobaricTensorSimplicityTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable {U : FinitePlace F → Type u} [∀ v, AddCommGroup (U v)] [∀ v, Module ℂ (U v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (U v)}
variable {E : Finset (FinitePlace F)}
variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
variable (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)

set_option maxHeartbeats 1600000 in
/-- The prescribed tensor is irreducible already as a model for the common
free operators, from the density of its finite and archimedean actions. -/
theorem targetTensorAction_isIrreducible
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :
    Representation.IsIrreducible (targetTensorAction A D real complex).toMonoidHom := by
  let fin := tensorRepresentation F (r + 1) (fun v => (A v).obj.representation)
    E D.targetReference D.target_fixed
  refine irreducible_tensorFreeAction F (r + 1) (fin := fin) ?_ ?_ ?_ ?_
  · let : fin.IsIrreducible := target_isIrreducible A D
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteAdelicGL F (r + 1))) fin.asModule
  · refine tensorRepresentation_exists_eq_on F (r + 1) _ E _ _ D.target_nonzero
      (fun v => (A v).property.1) ?_
    intro v
    refine Eq.mpr (congrArg (fun t =>
      @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (A v).obj.representation)
      (localGL_topology_eq F v (r + 1))) ?_
    exact (A v).property.2
  · intro v
    exact realStandardQuotient_density (r + 1) (real v).orderedBlocks (real v).stable (real v).irreducible
  · intro v
    exact complexStandardQuotient_density (r + 1) (complex v).orderedBlocks (complex v).stable (complex v).irreducible

local instance realizationRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance realizationContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance realizationSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance realizationFormsAddCommGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance realizationStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _

/-- The canonical action on the specified tensor is a quotient of a stable
automorphic subspace. -/
def HasTargetTensorSurjection
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) : Prop :=
  ∃ S : Subrepresentation
      ((stableAutomorphicAction F (r + 1)).comp (freeOperatorProjection F (r + 1)).toMonoidHom),
    ∃ q : S.toRepresentation.IntertwiningMap (targetTensorAction A D real complex).toMonoidHom,
      Function.Surjective q

set_option maxHeartbeats 1600000 in
/-- A surjective intertwiner from a stable automorphic subspace onto the
constructed tensor gives the prescribed realization. -/
theorem hasTensorRealization_of_targetSurjection
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v)
    (h : HasTargetTensorSurjection A D real complex) :
    HasTensorRealization A D
      (fun v => (real v).orderedBlocks) (fun v => (complex v).orderedBlocks)
      (fun v => (real v).kernel) (fun v => (complex v).kernel)
      (fun v => (real v).stable) (fun v => (complex v).stable) := by
  obtain ⟨S, q, hq⟩ := h
  refine ⟨(targetTensorAction A D real complex).toMonoidHom, ?_, S, q, hq⟩
  exact tensorFreeAction_hasActions F (r + 1) _ _ _ _ _

end Langlands.Global.CuspidalInducedFiniteTensor
