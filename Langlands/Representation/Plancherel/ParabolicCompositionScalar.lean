import Langlands.Representation.Plancherel.RationalUnramifiedScalarField
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation

/-! # Opposite scalars of two parabolics from composition identities -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI u₀ u₁ u₂ u₃

namespace UnramifiedOperatorFamily

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}

/-- Eight operator families between four carriers on one parameter set,
with the four composition identities used for two parabolic subgroups and
their opposites. Index `0` is `P`, `1` is `P'`, `2` is the opposite of
`P'` and `3` is the opposite of `P`; `J i j` goes from carrier `j` to
carrier `i`. -/
structure ParabolicCompositionData (R : Set (unramifiedCharacters ν))
    (X₀ : Type u₀) (X₁ : Type u₁) (X₂ : Type u₂) (X₃ : Type u₃)
    [AddCommGroup X₀] [Module ℂ X₀] [AddCommGroup X₁] [Module ℂ X₁]
    [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃] where
  /-- The family from `P` to `P'`. -/
  J₁₀ : R → X₀ →ₗ[ℂ] X₁
  /-- The family from the opposite of `P'` to `P`. -/
  J₀₂ : R → X₂ →ₗ[ℂ] X₀
  /-- The family from the opposite of `P` to the opposite of `P'`. -/
  J₂₃ : R → X₃ →ₗ[ℂ] X₂
  /-- The family from `P'` to the opposite of `P`. -/
  J₃₁ : R → X₁ →ₗ[ℂ] X₃
  /-- The family from the opposite of `P'` to `P'`. -/
  J₁₂ : R → X₂ →ₗ[ℂ] X₁
  /-- The family from `P'` to its opposite. -/
  J₂₁ : R → X₁ →ₗ[ℂ] X₂
  /-- The family from the opposite of `P` to `P`. -/
  J₀₃ : R → X₃ →ₗ[ℂ] X₀
  /-- The family from `P` to its opposite. -/
  J₃₀ : R → X₀ →ₗ[ℂ] X₃
  /-- `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}` at every parameter. -/
  comp₁₂ : ∀ χ, J₁₂ χ = (J₁₀ χ).comp (J₀₂ χ)
  /-- `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}` at every parameter. -/
  comp₂₁ : ∀ χ, J₂₁ χ = (J₂₃ χ).comp (J₃₁ χ)
  /-- `J_{P|P̄} = J_{P|P̄'} J_{P̄'|P̄}` at every parameter. -/
  comp₀₃ : ∀ χ, J₀₃ χ = (J₀₂ χ).comp (J₂₃ χ)
  /-- `J_{P̄|P} = J_{P̄|P'} J_{P'|P}` at every parameter. -/
  comp₃₀ : ∀ χ, J₃₀ χ = (J₃₁ χ).comp (J₁₀ χ)

namespace ParabolicCompositionData

variable {R : Set (unramifiedCharacters ν)}
  {X₀ : Type u₀} {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃}
  [AddCommGroup X₀] [Module ℂ X₀] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
  (d : ParabolicCompositionData R X₀ X₁ X₂ X₃)

/-- Both opposite composites act on `J₁₀` by the same multiple: if the
composite on carrier `0` is `c` and that on carrier `1` is `c'`, then
`c' J₁₀ = c J₁₀`. -/
theorem smul_J₁₀_eq (χ : R) (c c' : ℂ)
    (hc : (d.J₀₃ χ).comp (d.J₃₀ χ) = c • LinearMap.id)
    (hc' : (d.J₁₂ χ).comp (d.J₂₁ χ) = c' • LinearMap.id) :
    c' • d.J₁₀ χ = c • d.J₁₀ χ := by
  have h₁ : c' • d.J₁₀ χ = ((d.J₁₂ χ).comp (d.J₂₁ χ)).comp (d.J₁₀ χ) := by
    rw [hc']
    rfl
  have h₂ : c • d.J₁₀ χ = (d.J₁₀ χ).comp ((d.J₀₃ χ).comp (d.J₃₀ χ)) := by
    rw [hc]
    apply LinearMap.ext
    intro v
    simp
  rw [h₁, h₂, d.comp₁₂, d.comp₂₁, d.comp₀₃, d.comp₃₀]
  rfl

/-- At a parameter where `J₁₀` is nonzero the two scalars agree. -/
theorem scalar_eq (χ : R) (c c' : ℂ)
    (hc : (d.J₀₃ χ).comp (d.J₃₀ χ) = c • LinearMap.id)
    (hc' : (d.J₁₂ χ).comp (d.J₂₁ χ) = c' • LinearMap.id)
    (v : X₀) (hv : d.J₁₀ χ v ≠ 0) : c' = c := by
  have h := congrArg (fun T : X₀ →ₗ[ℂ] X₁ => T v) (d.smul_J₁₀_eq χ c c' hc hc')
  simp only [LinearMap.smul_apply] at h
  exact smul_left_injective ℂ hv h

end ParabolicCompositionData

variable {V : Type u₀} [AddCommGroup V] [Module ℂ V]
  {W : Type u₁} [AddCommGroup W] [Module ℂ W]

/-- A rational operator family on an open set that is nonzero at one point is
nonzero, already on one fixed vector, throughout a nonempty open subset. -/
theorem IsRationalOperatorOn.exists_isOpen_apply_ne_zero
    {R : Set (unramifiedCharacters ν)} (hR : IsOpen R)
    {A : R → V →ₗ[ℂ] W} (hA : IsRationalOperatorOn R A)
    (χ₀ : R) (hχ₀ : A χ₀ ≠ 0) :
    ∃ (D : Set (unramifiedCharacters ν)) (hDR : D ⊆ R) (v : V),
      IsOpen D ∧ D.Nonempty ∧ ∀ χ (hχ : χ ∈ D), A ⟨χ, hDR hχ⟩ v ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, A χ₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hχ₀ (LinearMap.ext h)
  obtain ⟨ℓ, hℓ⟩ := exists_normalized_scalar_functional (A χ₀ v) hv
  obtain ⟨b, hb, hpoly⟩ := hA
  obtain ⟨n, e, w, hexp⟩ := hpoly v
  let g : unramifiedRegularFunctions ν := ∑ i, ℓ (w i) • e i
  have hg : ∀ χ : R, g.val χ.val = b.val χ.val * ℓ (A χ v) := by
    intro χ
    have h := congrArg ℓ (hexp χ)
    simp only [LinearMap.smul_apply, map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    simp only [g, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨R ∩ {χ | g.val χ ≠ 0}, Set.inter_subset_left, v, ?_, ?_, ?_⟩
  · exact hR.inter (isOpen_compl_singleton.preimage
      (continuous_unramifiedRegularFunction ν g))
  · refine ⟨χ₀.val, χ₀.property, ?_⟩
    change g.val χ₀.val ≠ 0
    rw [hg χ₀, hℓ, mul_one]
    exact hb χ₀
  · intro χ hχ hzero
    apply hχ.2
    rw [hg ⟨χ, hχ.1⟩, hzero, map_zero, mul_zero]

end UnramifiedOperatorFamily

section ActualCharacters

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  {R : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {X₀ : Type u₀} {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃}
  [AddCommGroup X₀] [Module ℂ X₀] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]

include hp hG in
/-- If both opposite composites have regular fractional presentations on an
open set `R` carrying the composition identities, and the rational family
`J₁₀` is nonzero at one point of `R`, the two function field elements agree. -/
theorem ParabolicCompositionData.functionField_eq
    (d : ParabolicCompositionData R X₀ X₁ X₂ X₃) (hR : IsOpen R)
    (hJ : IsRationalOperatorOn R d.J₁₀) (χ₀ : R) (hχ₀ : d.J₁₀ χ₀ ≠ 0)
    (s s' : rationalUnramifiedFunctionField G hp hG)
    (a b a' b' : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : ∀ χ : R, b.val χ.val ≠ 0) (hb' : ∀ χ : R, b'.val χ.val ≠ 0)
    (hs : s =
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) a /
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) b)
    (hs' : s' =
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) a' /
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) b')
    (hc : ∀ χ : R, (d.J₀₃ χ).comp (d.J₃₀ χ) = (a.val χ.val / b.val χ.val) • LinearMap.id)
    (hc' : ∀ χ : R,
      (d.J₁₂ χ).comp (d.J₂₁ χ) = (a'.val χ.val / b'.val χ.val) • LinearMap.id) :
    s' = s := by
  obtain ⟨D, hDR, v, hD, hne, hv⟩ := hJ.exists_isOpen_apply_ne_zero hR χ₀ hχ₀
  have hRne : R.Nonempty := ⟨χ₀.val, χ₀.property⟩
  let p : ScalarPresentation R (fun χ => a.val χ.val / b.val χ.val) :=
    ⟨a, b, hb, fun χ => mul_div_cancel₀ _ (hb χ)⟩
  let p' : ScalarPresentation R (fun χ => a'.val χ.val / b'.val χ.val) :=
    ⟨a', b', hb', fun χ => mul_div_cancel₀ _ (hb' χ)⟩
  have hps : s = p.toFunctionField G hp hG hRne :=
    hs.trans (p.toFunctionField_eq_div G hp hG hRne).symm
  have hps' : s' = p'.toFunctionField G hp hG hRne :=
    hs'.trans (p'.toFunctionField_eq_div G hp hG hRne).symm
  rw [hps, hps']
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen G hp hG p' p hRne hRne
    hD hne hDR hDR
  intro χ hχ
  exact d.scalar_eq ⟨χ, hDR hχ⟩ _ _ (hc _) (hc' _) v (hv χ hχ)

end ActualCharacters

end Langlands.Plancherel
