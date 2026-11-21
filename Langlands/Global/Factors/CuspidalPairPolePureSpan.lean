import Langlands.Global.Factors.CuspidalPairPolePrescribedEqualTests

/-! # Generation by pure cuspidal vectors at a finite set of places -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

universe u uQ

open NumberField Set
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal InfinitePlaceFamily
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open Langlands.RestrictedTensor (Stage Index of transition of_transition)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance polePureSpanAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance polePureSpanSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance polePureSpanRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance polePureSpanContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance polePureSpanFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance polePureSpanAutomorphicGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance polePureSpanStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance polePureSpanSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T) (hP : HasIrreducibleAdmissibleComponents P)
  {S U : Finset (FinitePlace F)}

/-- The span of actual pure vectors with the fixed reference factors outside `S`. -/
def poleEqualPureSpan (hPS : P.exceptional ⊆ S) : Submodule ℂ T.Space :=
  Submodule.span ℂ {x | ∃ a b, poleEqualPureVector P hP hPS a b = x}

theorem poleEqualPureSpan_mono (hPS : P.exceptional ⊆ S) (hPU : P.exceptional ⊆ U) (hSU : S ⊆ U) :
    poleEqualPureSpan P hP hPS ≤ poleEqualPureSpan P hP hPU := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, rfl⟩
  apply Submodule.subset_span
  refine ⟨Langlands.RestrictedTensor.extend P.reference a, b, ?_⟩
  have he : P.finitePure U hPU (Langlands.RestrictedTensor.extend P.reference a) = P.finitePure S hPS a :=
    Langlands.RestrictedTensor.pure_extend (K := ℂ) P.tensorExceptional P.reference
      (S := ⟨S, P.unramified.exceptional_subset.trans hPS⟩)
      (T := ⟨U, P.unramified.exceptional_subset.trans hPU⟩) hSU a
  exact congrArg (fun y => P.allPlaceTensorEquiv hP (y ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) he

/-- Every vector in the span is spherical outside its retained set. -/
theorem sphericalOutside_of_mem_poleEqualPureSpan (hPS : P.exceptional ⊆ S)
    {x : T.Space} (hx : x ∈ poleEqualPureSpan P hP hPS) : IsSphericalOutside F T S x := by
  intro v hv k hk
  let A := T.realization.finiteRepresentation (FiniteAdelicGL.localInclusion F (r + 1) v k)
  change A x = x
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, b, rfl⟩ := hy
      exact poleEqualPureVector_sphericalOutside P hP hPS a b v hv k hk
  | zero => exact map_zero A
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

/-- Every element of a given finite tensor stage combined with an infinite tensor lies
in the span of the pure vectors on that stage. -/
private theorem image_of_stage_mem_poleEqualPureSpan (hPS : P.exceptional ⊆ S)
    (y : Stage ℂ (fun v => P.localFactor v) S)
    (z : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    P.allPlaceTensorEquiv hP
      (of ℂ (fun v => P.localFactor v) P.tensorExceptional P.reference
        ⟨S, P.unramified.exceptional_subset.trans hPS⟩ y ⊗ₜ[ℂ] z) ∈ poleEqualPureSpan P hP hPS := by
  let f := of ℂ (fun v => P.localFactor v) P.tensorExceptional P.reference
    ⟨S, P.unramified.exceptional_subset.trans hPS⟩
  let M := poleEqualPureSpan P hP hPS
  let J := P.allPlaceTensorEquiv hP
  change J (f y ⊗ₜ[ℂ] z) ∈ M
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c a =>
      have hp (b : ∀ i : InfinitePlaceFamily.Index F, T.placeDensityModels.subspace i) :
          J (f (PiTensorProduct.tprod ℂ a) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ∈ M :=
        Submodule.subset_span ⟨a, b, rfl⟩
      have hz : J (f (PiTensorProduct.tprod ℂ a) ⊗ₜ[ℂ] z) ∈ M := by
        induction z using PiTensorProduct.induction_on with
        | smul_tprod d b =>
            simpa only [TensorProduct.tmul_smul, map_smul] using M.smul_mem d (hp b)
        | add z₁ z₂ h₁ h₂ =>
            simpa only [TensorProduct.tmul_add, map_add] using M.add_mem h₁ h₂
      simpa only [map_smul, ← TensorProduct.smul_tmul'] using M.smul_mem c hz
  | add y₁ y₂ h₁ h₂ =>
      simpa only [map_add, TensorProduct.add_tmul] using M.add_mem h₁ h₂

/-- An arbitrary cuspidal vector belongs to the span of the pure vectors after enlarging
any specified finite set. -/
theorem exists_mem_poleEqualPureSpan (B : Finset (FinitePlace F)) (x : T.Space) :
    ∃ U : Finset (FinitePlace F), B ⊆ U ∧ ∃ hPU : P.exceptional ⊆ U, x ∈ poleEqualPureSpan P hP hPU := by
  let J := P.allPlaceTensorEquiv hP
  obtain ⟨t, rfl⟩ := J.surjective x
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      obtain ⟨V, y, rfl⟩ := Langlands.RestrictedTensor.exists_of P.tensorExceptional P.reference a
      let U := (B ∪ P.exceptional) ∪ V.val
      have hBU : B ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
      have hPU : P.exceptional ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
      have hVU : V.val ⊆ U := Finset.subset_union_right
      let U₀ : Langlands.RestrictedTensor.Index P.tensorExceptional :=
        ⟨U, P.unramified.exceptional_subset.trans hPU⟩
      have h := image_of_stage_mem_poleEqualPureSpan P hP hPU (transition P.reference hVU y) b
      have he := of_transition P.tensorExceptional P.reference (S := V) (T := U₀) hVU y
      exact ⟨U, hBU, hPU, (congrArg (fun a => J (a ⊗ₜ[ℂ] b)) he) ▸ h⟩
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨U₁, hBU₁, hPU₁, hm₁⟩ := h₁
      obtain ⟨U₂, _, hPU₂, hm₂⟩ := h₂
      let U := U₁ ∪ U₂
      have hPU : P.exceptional ⊆ U := hPU₁.trans Finset.subset_union_left
      refine ⟨U, hBU₁.trans Finset.subset_union_left, hPU, ?_⟩
      rw [map_add]
      exact (poleEqualPureSpan P hP hPU).add_mem
        (poleEqualPureSpan_mono P hP hPU₁ hPU Finset.subset_union_left hm₁)
        (poleEqualPureSpan_mono P hP hPU₂ hPU Finset.subset_union_right hm₂)

end Langlands.Global.CuspidalPairPoles
