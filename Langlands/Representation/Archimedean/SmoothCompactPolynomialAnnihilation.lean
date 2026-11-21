import Langlands.Automorphic.CuspidalAdmissible.FixedMultiplicity
import Langlands.Representation.Archimedean.SmoothCompactAdmissibility
import Langlands.Representation.Archimedean.SmoothUnitAction
import Langlands.Representation.KFiniteDual
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-! # Monic annihilation of compact-finite smooth vectors by compact-commuting operators -/

noncomputable section

open scoped Manifold ContDiff Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))
  (K : Subgroup Aˣ)

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

/-- The genuine smooth action restricted to a subgroup of the units. -/
abbrev subgroupRepresentation : Representation ℂ K D :=
  (representation 𝓜 R).comp K.subtype

/-- Postcomposition by an operator commuting with the subgroup action, as an endomorphism
of each smooth intertwiner space. -/
def postcompIntertwiners (Ω : Module.End ℂ D)
    (hΩ : ∀ (k : K) (w : D),
      Ω (representation 𝓜 R (k : Aˣ) w) = representation 𝓜 R (k : Aˣ) (Ω w))
    (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (smoothIntertwiners 𝓜 R K d τ) :=
  LinearMap.restrict (LinearMap.llcomp ℂ (Fin d → ℂ) D D Ω) fun T hT => by
    have hT' : ∀ (k : K) (x : Fin d → ℂ),
        T (τ k *ᵥ x) = representation 𝓜 R (k : Aˣ) (T x) := hT
    intro k x
    change Ω (T (τ k *ᵥ x)) = representation 𝓜 R (k : Aˣ) (Ω (T x))
    rw [hT' k x, hΩ]

@[simp]
theorem postcompIntertwiners_apply (Ω : Module.End ℂ D)
    (hΩ : ∀ (k : K) (w : D),
      Ω (representation 𝓜 R (k : Aˣ) w) = representation 𝓜 R (k : Aˣ) (Ω w))
    (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) (T : smoothIntertwiners 𝓜 R K d τ)
    (x : Fin d → ℂ) :
    (postcompIntertwiners R K Ω hΩ d τ T : (Fin d → ℂ) →ₗ[ℂ] D) x = Ω ((T : _ →ₗ[ℂ] D) x) :=
  rfl

variable [FiniteDimensional ℝ A]

/-- If the genuine smooth action is admissible for the subgroup, every vector with a
finite-dimensional orbit span under the subgroup is annihilated by a monic polynomial in
any operator commuting with the subgroup action. -/
theorem exists_monic_aeval_eq_zero_of_isFiniteVector (hR : IsContinuousRepresentation R)
    (hadm : IsAdmissible 𝓜 R K) (Ω : Module.End ℂ D)
    (hΩ : ∀ (k : K) (w : D),
      Ω (representation 𝓜 R (k : Aˣ) w) = representation 𝓜 R (k : Aˣ) (Ω w))
    {v : D} (hv : FiniteVectors.IsFiniteVector (subgroupRepresentation R K) v) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval Ω p v = 0 := by
  let ρ := subgroupRepresentation R K
  let S := FiniteVectors.orbitSubrepresentation ρ v
  let : FiniteDimensional ℂ S.toSubmodule := hv
  let d := Module.finrank ℂ S.toSubmodule
  let b := Module.finBasis ℂ S.toSubmodule
  let τ := Langlands.KFiniteDual.subMatrix S
  have hτ : Continuous τ := by
    refine continuous_matrix fun i l => ?_
    have h : Continuous (fun k : K => S.toRepresentation k (b l)) :=
      ((continuous_representation_units R hR).comp
        (continuous_subtype_val.prodMk continuous_const)).subtype_mk _
    exact ((b.coord i).toContinuousLinearMap.continuous.comp h).congr
      (fun k => (Langlands.KFiniteDual.subMatrix_apply S k i l).symm)
  let Q := smoothIntertwiners 𝓜 R K d τ
  let : FiniteDimensional ℂ Q := hadm d τ hτ
  let Ωt := postcompIntertwiners R K Ω hΩ d τ
  obtain ⟨p, hp, hpz⟩ := LinearMap.exists_monic_and_aeval_eq_zero (M := Q) ℂ Ωt
  let T0 : Q := ⟨S.toSubmodule.subtype.comp b.equivFun.symm.toLinearMap, by
    intro k x
    change ((b.equivFun.symm (τ k *ᵥ x) : S.toSubmodule) : D) =
      representation 𝓜 R (k : Aˣ) ((b.equivFun.symm x : S.toSubmodule) : D)
    rw [← Langlands.KFiniteDual.coordRep_apply, Langlands.KFiniteDual.equivFun_symm_coordRep]
    rfl⟩
  let vS : S.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  let ev : Q →ₗ[ℂ] D := (LinearMap.applyₗ (b.equivFun vS)).comp Q.subtype
  have hev : ∀ T, ev (Ωt T) = Ω (ev T) := fun T => rfl
  have key := Langlands.Automorphic.map_aeval_apply Ωt Ω ev hev p T0
  rw [hpz, LinearMap.zero_apply, map_zero] at key
  have hT0 : ev T0 = v := by
    change ((b.equivFun.symm (b.equivFun vS) : S.toSubmodule) : D) = v
    rw [LinearEquiv.symm_apply_apply]
  exact ⟨p, hp, by rw [← hT0, ← key]⟩

end Langlands.Archimedean.DerivativeSmoothVectors
