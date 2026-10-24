/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper

Modified by Worker 230 (2026): adapt the canonical integral tensor maps from
Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/Completion/BaseChange.lean:364-376, :810-821 and :836-844. Use the
Library's FinitePlacesAbove, finiteTensorMap and scoped FiniteExtension completion
algebra, retain independent universes, and add the coefficient transport to
finiteTensorMap and the index equivalence. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.Inclusion

/-! # Canonical integral tensor maps at a finite place -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteExtension

universe u v

variable {K : Type u} (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

namespace FiniteExtension

/-- Scalar coherence for the completed integers: `𝓞 K` acts on `K_p` through `O_p`.
Needed because instance search chooses the ring-of-integers action of `𝓞 K` on `K_p`. -/
scoped instance isScalarTower_ringOfIntegers_adicCompletionIntegers
    (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (p.adicCompletionIntegers K) (p.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Scalar coherence for a completion of `L`: `𝓞 K` acts on `L_q` through `𝓞 L`. -/
scoped instance isScalarTower_ringOfIntegers_adicCompletion (q : HeightOneSpectrum (𝓞 L)) :
    IsScalarTower (𝓞 K) (𝓞 L) (q.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end FiniteExtension

/-- The canonical `𝓞 L`-linear map `𝓞 L ⊗[𝓞 K] O_p → 𝓞 L ⊗[𝓞 K] K_p` induced by the
inclusion of the completed integers. No injectivity is asserted. -/
def integralTensorInclusion (p : HeightOneSpectrum (𝓞 K)) :
    𝓞 L ⊗[𝓞 K] p.adicCompletionIntegers K →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] p.adicCompletion K :=
  TensorProduct.AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L)
    (Algebra.algHom (𝓞 K) (p.adicCompletionIntegers K) (p.adicCompletion K)).toLinearMap

omit [NumberField L] in
@[simp] theorem integralTensorInclusion_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletionIntegers K) :
    integralTensorInclusion L p (b ⊗ₜ[𝓞 K] x) = b ⊗ₜ[𝓞 K] (x : p.adicCompletion K) := rfl

/-- The canonical `𝓞 L`-algebra comparison from `𝓞 L ⊗[𝓞 K] K_p` to the product of the
completions above `p`. Its bijectivity is a separate obligation. -/
def integralTensorComparisonAlgHom (p : HeightOneSpectrum (𝓞 K)) :
    𝓞 L ⊗[𝓞 K] p.adicCompletion K →ₐ[𝓞 L]
      ((q : FinitePlacesAbove L p) → q.1.adicCompletion L) :=
  AlgHom.pi fun q =>
    Algebra.TensorProduct.lift (Algebra.ofId (𝓞 L) (q.1.adicCompletion L))
      ((Algebra.algHom K (p.adicCompletion K) (q.1.adicCompletion L)).restrictScalars (𝓞 K))
      (fun _ _ => .all _ _)

/-- The comparison `T_p` as an `𝓞 L`-linear map. -/
def integralTensorComparison (p : HeightOneSpectrum (𝓞 K)) :
    𝓞 L ⊗[𝓞 K] p.adicCompletion K →ₗ[𝓞 L]
      ((q : FinitePlacesAbove L p) → q.1.adicCompletion L) :=
  (integralTensorComparisonAlgHom L p).toLinearMap

@[simp] theorem integralTensorComparison_apply (p : HeightOneSpectrum (𝓞 K))
    (z : 𝓞 L ⊗[𝓞 K] p.adicCompletion K) :
    integralTensorComparison L p z = integralTensorComparisonAlgHom L p z := rfl

@[simp] theorem integralTensorComparisonAlgHom_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletion K) (q : FinitePlacesAbove L p) :
    integralTensorComparisonAlgHom L p (b ⊗ₜ[𝓞 K] x) q =
      algebraMap (𝓞 L) (q.1.adicCompletion L) b * FiniteExtension.completionMap p q.1 x := rfl

theorem integralTensorComparison_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletion K) (q : FinitePlacesAbove L p) :
    integralTensorComparison L p (b ⊗ₜ[𝓞 K] x) q =
      algebraMap (𝓞 L) (q.1.adicCompletion L) b * FiniteExtension.completionMap p q.1 x := rfl

theorem integralTensorComparison_integralTensorInclusion_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletionIntegers K) (q : FinitePlacesAbove L p) :
    integralTensorComparison L p (integralTensorInclusion L p (b ⊗ₜ[𝓞 K] x)) q =
      algebraMap (𝓞 L) (q.1.adicCompletion L) b *
        (FiniteExtension.completionIntegersMap p q.1 x : q.1.adicCompletion L) := rfl

/-- The coefficient and tensor-order transport `𝓞 L ⊗[𝓞 K] K_p → K_p ⊗[K] L`. -/
def integralTensorTransport (p : HeightOneSpectrum (𝓞 K)) :
    𝓞 L ⊗[𝓞 K] p.adicCompletion K →ₐ[𝓞 K] p.adicCompletion K ⊗[K] L :=
  @Algebra.TensorProduct.lift (𝓞 K) (𝓞 K) (𝓞 L) (p.adicCompletion K)
    (p.adicCompletion K ⊗[K] L) _ _ _ _ _ _ _ _ _ _ _ _
    (IsScalarTower.of_algebraMap_eq fun _ => rfl)
    ((Algebra.TensorProduct.includeRight.restrictScalars (𝓞 K)).comp
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L))
    ((Algebra.TensorProduct.includeLeft (S := K)).restrictScalars (𝓞 K))
    (fun _ _ => .all _ _)

omit [NumberField L] in
@[simp] theorem integralTensorTransport_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletion K) :
    integralTensorTransport L p (b ⊗ₜ[𝓞 K] x) = x ⊗ₜ[K] algebraMap (𝓞 L) L b := by
  simp [integralTensorTransport]

theorem finiteTensorMap_integralTensorTransport (p : HeightOneSpectrum (𝓞 K))
    (z : 𝓞 L ⊗[𝓞 K] p.adicCompletion K) :
    finiteTensorMap p (integralTensorTransport L p z) = integralTensorComparison L p z := by
  induction z with
  | tmul b x =>
    funext q
    rw [integralTensorTransport_tmul, finiteTensorMap_tmul, integralTensorComparison_tmul,
      mul_comm, ← IsScalarTower.algebraMap_apply]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]

/-- Places above `p` are exactly the primes of `𝓞 L` whose restriction to `𝓞 K` is `p`;
the underlying prime is unchanged. -/
def finitePlacesAboveEquiv (p : HeightOneSpectrum (𝓞 K)) :
    FinitePlacesAbove L p ≃ {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p} where
  toFun q := ⟨q.1, finitePlacesAbove_under p q⟩
  invFun q := ⟨q.1, by obtain ⟨q, rfl⟩ := q; exact liesOver_under q⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField K] in
@[simp] theorem finitePlacesAboveEquiv_apply_coe (p : HeightOneSpectrum (𝓞 K))
    (q : FinitePlacesAbove L p) :
    (finitePlacesAboveEquiv L p q : HeightOneSpectrum (𝓞 L)) = q.1 := rfl

omit [NumberField K] in
@[simp] theorem finitePlacesAboveEquiv_symm_apply_coe (p : HeightOneSpectrum (𝓞 K))
    (q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}) :
    ((finitePlacesAboveEquiv L p).symm q).1 = q.1 := rfl

end Langlands.Global.AdelicFunctoriality
