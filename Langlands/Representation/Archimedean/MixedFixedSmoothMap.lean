import Langlands.Representation.Archimedean.MixedSmoothVectors

/-! # Pullback from mixed smooth vectors through a fixed Hilbert level -/

noncomputable section
open scoped Manifold ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Archimedean.MixedSmooth

open DerivativeSmoothVectors SmoothInvariantSubspace
universe uA uB uG uH uL uE uV

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {B : Type uB} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace B H] [LieGroup 𝓘(ℝ, B) ∞ H]
  {L : Type uL} [Group L] [TopologicalSpace L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (σ : L →* (E →L[ℂ] E)) (π : H →* (E →L[ℂ] E))
  (hcomm : ∀ g d v, π g (σ d v) = σ d (π g v))
  (U : OpenSubgroup L) (ρ : G →* (V →L[ℂ] V))

local notation "I" => 𝓘(ℝ, A)
local notation "J" => 𝓘(ℝ, B)
local notation "P" => fixedRestriction σ U.toSubgroup π hcomm
local notation "W" => Vectors (A := B) σ π hcomm
local notation "F" => fixedSubspace σ U.toSubgroup

variable (M : DerivativeSmoothVectors 𝓘(ℝ, A) ρ →L[ℂ]
    DerivativeSmoothVectors 𝓘(ℝ, B) (fixedRestriction σ U.toSubgroup π hcomm))

private def smoothMap : smoothVectors I ρ →ₗ[ℂ] smoothVectors J π :=
  (SmoothInvariantSubspace.smoothInclusion π F
    (fixedSubspace_invariant σ U.toSubgroup π hcomm) J).comp
    ((toSmooth J P).toLinearMap.comp (M.toLinearMap.comp (toSmooth I ρ).symm.toLinearMap))

/-- A smooth map into a fixed Hilbert level has finite-smooth image in the ambient space. -/
def ofFixedDerivativeMap : smoothVectors I ρ →ₗ[ℂ] W where
  toFun v := ofFixed σ π hcomm U (smoothMap σ π hcomm U ρ M v)
    (toSmooth J P (M ((toSmooth I ρ).symm v)) : F).property
  map_add' v w := Subtype.ext (map_add (smoothMap σ π hcomm U ρ M) v w)
  map_smul' a v := Subtype.ext (map_smul (smoothMap σ π hcomm U ρ M) a v)

@[simp]
theorem ofFixedDerivativeMap_val (v : smoothVectors I ρ) :
    (ofFixedDerivativeMap σ π hcomm U ρ M v).val.val =
      ((toSmooth J P (M ((toSmooth I ρ).symm v)) : F) : E) :=
  rfl

/-- Pullback preserves derivative continuity if evaluation on the specified
fixed level is given by a derivative-continuous ambient functional. -/
theorem isContinuousOnSmoothVectors_comp_ofFixedDerivativeMap
    (ℓ : W →ₗ[ℂ] ℂ) (f : smoothVectors J π →ₗ[ℂ] ℂ)
    (hf : IsContinuousOnSmoothVectors J π f)
    (hfℓ : ∀ w : W, w.val.val ∈ F → ℓ w = f w.val) :
    IsContinuousOnSmoothVectors I ρ (ℓ.comp (ofFixedDerivativeMap σ π hcomm U ρ M)) := by
  let inc := derivativeInclusion π F (fixedSubspace_invariant σ U.toSubgroup π hcomm) J
  have hcont := (continuous_of_isContinuousOnSmoothVectors J π f hf).comp
    (inc.continuous.comp M.continuous)
  apply isContinuousOnSmoothVectors_of_continuous
  refine hcont.congr fun v => ?_
  let x := ofFixedDerivativeMap σ π hcomm U ρ M (toSmooth I ρ v)
  have hx : x.val.val ∈ F := (toSmooth J P (M ((toSmooth I ρ).symm (toSmooth I ρ v))) : F).property
  change f (toSmooth J π (inc (M v))) = ℓ x
  rw [hfℓ x hx]
  apply congrArg f
  apply Subtype.ext
  change ((toSmooth J P (M v) : F) : E) = x.val.val
  rw [ofFixedDerivativeMap_val, LinearEquiv.symm_apply_apply]

variable (i : G →* H) (T : V →L[ℂ] E)
  (hT : ∀ g v, T (ρ g v) = π (i g) (T v))
  (hM : ∀ v : DerivativeSmoothVectors 𝓘(ℝ, A) ρ,
    ((toSmooth 𝓘(ℝ, B) (fixedRestriction σ U.toSubgroup π hcomm) (M v) :
      fixedSubspace σ U.toSubgroup) : E) = T (toSmooth 𝓘(ℝ, A) ρ v))

include hT hM in
/-- If the lifted map agrees with an ambient intertwiner, it has the same covariance. -/
theorem ofFixedDerivativeMap_smoothRepresentation (g : G) (v : smoothVectors I ρ) :
    ofFixedDerivativeMap σ π hcomm U ρ M (smoothRepresentation I ρ g v) =
      archimedeanRepresentation σ π hcomm (i g) (ofFixedDerivativeMap σ π hcomm U ρ M v) := by
  have ht (z : smoothVectors I ρ) : (ofFixedDerivativeMap σ π hcomm U ρ M z).val.val = T z := by
    rw [ofFixedDerivativeMap_val, hM, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  rw [ht, archimedeanRepresentation_val]
  change T (ρ g v) = π (i g) (ofFixedDerivativeMap σ π hcomm U ρ M v).val.val
  rw [ht]
  exact hT g v

include hT hM in
/-- A mixed evaluation with the prescribed character along the local subgroup
pulls back to a genuine continuous local Whittaker functional. -/
theorem isWhittakerFunctional_comp_ofFixedDerivativeMap
    (N : Subgroup G) (χ : N →* ℂˣ)
    (ℓ : W →ₗ[ℂ] ℂ) (f : smoothVectors J π →ₗ[ℂ] ℂ)
    (hf : IsContinuousOnSmoothVectors J π f)
    (hfℓ : ∀ w : W, w.val.val ∈ F → ℓ w = f w.val)
    (hχ : ∀ u : N, ∀ w : W, ℓ (archimedeanRepresentation σ π hcomm (i u) w) = (χ u : ℂ) * ℓ w) :
    IsWhittakerFunctional I ρ N χ (ℓ.comp (ofFixedDerivativeMap σ π hcomm U ρ M)) := by
  refine ⟨isContinuousOnSmoothVectors_comp_ofFixedDerivativeMap σ π hcomm U ρ M ℓ f hf hfℓ, ?_⟩
  intro u v
  change ℓ (ofFixedDerivativeMap σ π hcomm U ρ M (smoothRepresentation I ρ (u : G) v)) = _
  rw [ofFixedDerivativeMap_smoothRepresentation σ π hcomm U ρ M i T hT hM]
  exact hχ u _

end Langlands.Archimedean.MixedSmooth
