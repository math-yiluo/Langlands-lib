import Langlands.Automorphic.CuspidalAdmissible.FixedMultiplicity
import Langlands.Representation.Archimedean.MixedOrbitClosure
import Langlands.Representation.Archimedean.RealCartanSquareSum
import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.KFiniteDual
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-! # Group invariance of the norm closure of a real Harish-Chandra image -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe uV uE₀ uE

attribute [local instance 100] LieRing.ofAssociativeRing

section Admissible

variable {K : Type*} [Group K] [TopologicalSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

private theorem exists_monic_annihilating_of_admissible
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) (Ω : Module.End ℂ V)
    (hΩ : ∀ (k : K) (v : V), Ω (ρ k v) = ρ k (Ω v))
    (v : V) (hv : FiniteVectors.IsFiniteVector ρ v) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval Ω p v = 0 := by
  let S := FiniteVectors.orbitSubrepresentation ρ v
  let : FiniteDimensional ℂ S.toSubmodule := hv
  let d := Module.finrank ℂ S.toSubmodule
  let b := Module.finBasis ℂ S.toSubmodule
  let τ := KFiniteDual.subMatrix S
  let Q := gkIntertwiners ρ d τ
  let : FiniteDimensional ℂ Q := hadm d τ (KFiniteDual.continuous_subMatrix hcont S)
  let ΩQ : Module.End ℂ Q :=
    LinearMap.restrict (LinearMap.llcomp ℂ (Fin d → ℂ) V V Ω) fun T hT => by
      have hT' : ∀ (k : K) (x : Fin d → ℂ), T (τ k *ᵥ x) = ρ k (T x) := hT
      intro k x
      change Ω (T (τ k *ᵥ x)) = ρ k (Ω (T x))
      rw [hT' k x, hΩ]
  obtain ⟨p, hp, hpQ⟩ := LinearMap.exists_monic_and_aeval_eq_zero (M := Q) ℂ ΩQ
  let T : Q := ⟨S.toSubmodule.subtype.comp b.equivFun.symm.toLinearMap, fun k x => by
    change ((b.equivFun.symm (τ k *ᵥ x) : S.toSubmodule) : V) =
      ρ k ((b.equivFun.symm x : S.toSubmodule) : V)
    rw [← KFiniteDual.coordRep_apply, KFiniteDual.equivFun_symm_coordRep]
    rfl⟩
  let vS : S.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  let ev : Q →ₗ[ℂ] V := (LinearMap.applyₗ (b.equivFun vS)).comp Q.subtype
  have he : ev T = v := by
    change ((b.equivFun.symm (b.equivFun vS) : S.toSubmodule) : V) = v
    rw [LinearEquiv.symm_apply_apply]
  have h := Langlands.Automorphic.map_aeval_apply ΩQ Ω ev (fun _ => rfl) p T
  rw [hpQ, LinearMap.zero_apply, map_zero, he] at h
  exact ⟨p, hp, h.symm⟩

end Admissible

open Langlands.Global Langlands.Global.ArchimedeanGL
open DerivativeSmoothVectors

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "L" n:max => ℂ ⊗[ℝ] (M n)
local notation "I" n:max => matrixModel ℝ n
local notation "D" n:max R:max => DerivativeSmoothVectors (I n) R

private def algebraicCartanSquareSum (n : ℕ) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : (L n) →ₗ⁅ℂ⁆ Module.End ℂ V) : Module.End ℂ V :=
  ∑ i, π (1 ⊗ₜ[ℝ] RealCartan.realCartanBasis n i) * π (1 ⊗ₜ[ℝ] RealCartan.realCartanBasis n i)

private theorem map_algebraicCartanSquareSum {n : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (K n) V} {π : (L n) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : G n →* (E →L[ℂ] E)}
    {f : V →ₗ[ℂ] D n R} (hf : IsSmoothGKIntertwiner ℝ n R ρ π f) (v : V) :
    f (algebraicCartanSquareSum n π v) =
      MixedOrbit.transportedCartanSquareSum ℚ n (rationalMixedMatrixEquiv n) R (f v) := by
  rw [RealCartan.transportedCartanSquareSum_eq, basisSquareSum_apply]
  simp only [algebraicCartanSquareSum, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hf.2]

/-- Suppose an admissible real Harish-Chandra module embeds into a genuine smooth carrier.
For any compact and Lie equivariant linear map to another genuine smooth carrier, the
norm closure of the underlying image is invariant under the whole real group. -/
def RealSmoothGKImageClosureStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K n) V) (π : (L n) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₀ : Type uE₀) [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    (R₀ : G n →* (E₀ →L[ℂ] E₀)) (e : V →ₗ[ℂ] D n R₀)
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : G n →* (E →L[ℂ] E)) (f : V →ₗ[ℂ] D n R),
    IsRealGKModule n ρ π → IsAdmissibleGKModule ρ → Function.Injective e →
    IsSmoothGKIntertwiner ℝ n R₀ ρ π e → IsContinuousRepresentation R →
    IsSmoothGKIntertwiner ℝ n R ρ π f →
    let W := ((derivativeCLM (I n) R []).toLinearMap.comp f).range.topologicalClosure
    ∀ (g : G n) (w : E), w ∈ W → R g w ∈ W

/-- Admissibility gives a monic annihilator in the Cartan square sum on every vector.
Transporting this annihilator to the smooth image gives the norm-closure invariance. -/
theorem realSmoothGKImageClosure : RealSmoothGKImageClosureStatement.{uV, uE₀, uE} := by
  intro n V _ _ ρ π E₀ _ _ R₀ e E _ _ R f hGK hadm heinj he hR hf
  classical
  let ψ := rationalMixedMatrixEquiv n
  let Ω := algebraicCartanSquareSum n π
  have hΩ (k : K n) (v : V) : Ω (ρ k v) = ρ k (Ω v) := by
    apply heinj
    rw [map_algebraicCartanSquareSum he, he.1, he.1, map_algebraicCartanSquareSum he]
    exact RealCartan.transportedCartanSquareSum_representation n R₀ k.prop (e v)
  let W := f.range
  have hWX (X : RealLieAlgebra ℚ n) (w : D n R) (hw : w ∈ W) :
      operator (I n) R (ψ (realLieAlgebraToMatrix ℚ n X)) w ∈ W := by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨_, hf.2 _ _⟩
  have hWK (k : G n) (hk : k ∈ unitaryCompact ℝ n) (w : D n R) (hw : w ∈ W) :
      representation (I n) R k w ∈ W := by
    obtain ⟨v, rfl⟩ := hw
    let κ : K n := ⟨(k : M n), hk⟩
    have hκ : Unitary.toUnits κ = k := Units.ext rfl
    exact ⟨ρ κ v, (hf.1 κ v).trans (by rw [hκ])⟩
  have hpoly (w : D n R) (hw : w ∈ W) :
      ∃ p : Polynomial ℂ, p.Monic ∧
        Polynomial.aeval (MixedOrbit.transportedCartanSquareSum ℚ n ψ R) p w = 0 := by
    obtain ⟨v, rfl⟩ := hw
    obtain ⟨p, hp, h⟩ := exists_monic_annihilating_of_admissible hGK.2.1 hadm Ω hΩ v (hGK.1 v)
    refine ⟨p, hp, ?_⟩
    rw [← Langlands.Automorphic.map_aeval_apply Ω _ f (map_algebraicCartanSquareSum hf), h, map_zero]
  have hclos := MixedOrbit.representation_mem_closure_of_stable ℚ n ψ R
    (unitaryCompact ℝ n) hR W hWX hWK hpoly
    (RealCartan.exists_unitaryCompact_mem_connectedComponent n)
  let ε := (derivativeCLM (I n) R []).toLinearMap
  let C := (W.map ε).topologicalClosure
  have hC (g : G n) (w : E) (hw : w ∈ C) : R g w ∈ C := by
    have hle : W.map ε ≤ C.comap (R g).toLinearMap := by
      rintro _ ⟨z, hz, rfl⟩
      exact hclos g hz
    exact Submodule.topologicalClosure_minimal _ hle
      ((Submodule.isClosed_topologicalClosure _).preimage (R g).continuous) hw
  simpa only [C, W, ε, LinearMap.range_comp] using hC

end Langlands.Archimedean
