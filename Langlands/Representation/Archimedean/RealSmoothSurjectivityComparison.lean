import Langlands.Representation.Archimedean.RealSmoothQuotientWordLift

/-! # Detecting smooth surjectivity in a second real representation -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

universe uE uF uX

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  (R : G n →* (E →L[ℂ] E)) (S : G n →* (F →L[ℂ] F))

/-- A continuous compact-equivariant map injective on the genuine compact-finite
vectors is injective on the genuine smooth carrier. -/
theorem injective_of_injective_smoothKFinite (hR : IsContinuousRepresentation R)
    (J : DerivativeSmoothVectors (I n) R →L[ℂ] DerivativeSmoothVectors (I n) S)
    (hJ : ∀ (k : K n) x, J (representation (I n) R (Unitary.toUnits k) x) =
      representation (I n) S (Unitary.toUnits k) (J x))
    (h₀ : Function.Injective (fun x : smoothKFinite ℝ n R => J x.val)) : Function.Injective J := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  let U := J.toLinearMap.ker
  have hU (k : K n) (v : DerivativeSmoothVectors (I n) R) (hv : v ∈ U) :
      representation (I n) R (Unitary.toUnits k) v ∈ U := by
    change J v = 0 at hv
    change J (representation (I n) R (Unitary.toUnits k) v) = 0
    rw [hJ, hv, map_zero]
  have hs := le_topologicalClosure_smoothKFinite_inf R hR U J.isClosed_ker hU hx
  change x ∈ closure ((smoothKFinite ℝ n R ⊓ U) : Set (DerivativeSmoothVectors (I n) R)) at hs
  have hsub : ((smoothKFinite ℝ n R ⊓ U) : Set (DerivativeSmoothVectors (I n) R)) ⊆ {0} := by
    rintro y ⟨hy, hker⟩
    have he : J (⟨y, hy⟩ : smoothKFinite ℝ n R).val = J (0 : smoothKFinite ℝ n R).val := by
      change J y = J 0
      rw [map_zero]
      exact hker
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (h₀ he))
  exact Set.mem_singleton_iff.mp (closure_minimal hsub isClosed_singleton hs)

/-- The range of a map dense in a genuine smooth carrier can be checked after a
compact-equivariant continuous map that is injective on compact-finite vectors. -/
def RealSmoothSurjectivityComparisonStatement : Prop :=
  ∀ (n : ℕ) (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (R : G n →* (E →L[ℂ] E)) (S : G n →* (F →L[ℂ] F))
    (J : DerivativeSmoothVectors (I n) R →L[ℂ] DerivativeSmoothVectors (I n) S),
    IsContinuousRepresentation R →
    (∀ (k : K n) x, J (representation (I n) R (Unitary.toUnits k) x) =
      representation (I n) S (Unitary.toUnits k) (J x)) →
    Function.Injective (fun x : smoothKFinite ℝ n R => J x.val) →
    ∀ (X : Type uX) (Q : X → DerivativeSmoothVectors (I n) R),
      DenseRange Q → IsClosed (Set.range (J ∘ Q)) → Function.Surjective Q

theorem realSmoothSurjectivityComparison : RealSmoothSurjectivityComparisonStatement.{uE, uF, uX} := by
  intro n E _ _ _ F _ _ R S J hR hJ h₀ X Q hQ hclosed
  have hj := injective_of_injective_smoothKFinite R S hR J hJ h₀
  intro y
  have hmap : Set.MapsTo J (Set.range Q) (Set.range (J ∘ Q)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hy := hmap.closure_left J.continuous hclosed (hQ y)
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hj hx⟩

end Langlands.Archimedean
