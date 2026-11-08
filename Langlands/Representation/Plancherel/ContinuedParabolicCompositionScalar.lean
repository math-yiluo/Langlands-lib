import Langlands.Representation.Plancherel.ParabolicCompositionScalar
import Langlands.Representation.Plancherel.ContinuedIntertwiningComposition
import Langlands.Representation.Plancherel.ContinuedIntertwiningScalar

/-! # Equality of two continued opposite scalars from composition on open sets -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI uV uW uZ u₀ u₁ u₂ u₃

namespace UnramifiedOperatorFamily

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} {ν : I → (H →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {Ω₀ Ω₁ Ω₂ : Set (unramifiedCharacters ν)}

/-- The family `C` is the composite `B ∘ A` on some nonempty open set of
parameters contained in the regions of all three families. -/
def HasOpenComposition (A : Ω₀ → V →ₗ[ℂ] W) (B : Ω₁ → W →ₗ[ℂ] Z)
    (C : Ω₂ → V →ₗ[ℂ] Z) : Prop :=
  ∃ D : Set (unramifiedCharacters ν), IsOpen D ∧ D.Nonempty ∧
    ∃ (hD₀ : D ⊆ Ω₀) (hD₁ : D ⊆ Ω₁) (hD₂ : D ⊆ Ω₂),
      ∀ χ (hχ : χ ∈ D), C ⟨χ, hD₂ hχ⟩ = (B ⟨χ, hD₁ hχ⟩).comp (A ⟨χ, hD₀ hχ⟩)

namespace HasOpenComposition

variable {A : Ω₀ → V →ₗ[ℂ] W} {B : Ω₁ → W →ₗ[ℂ] Z} {C : Ω₂ → V →ₗ[ℂ] Z}

/-- The region of the first factor is nonempty. -/
theorem nonempty_first (h : HasOpenComposition A B C) : Ω₀.Nonempty := by
  obtain ⟨D, -, hne, hD₀, -, -, -⟩ := h
  exact hne.mono hD₀

/-- The region of the second factor is nonempty. -/
theorem nonempty_second (h : HasOpenComposition A B C) : Ω₁.Nonempty := by
  obtain ⟨D, -, hne, -, hD₁, -, -⟩ := h
  exact hne.mono hD₁

/-- The region of the composite family is nonempty. -/
theorem nonempty_third (h : HasOpenComposition A B C) : Ω₂.Nonempty := by
  obtain ⟨D, -, hne, -, -, hD₂, -⟩ := h
  exact hne.mono hD₂

end HasOpenComposition

end UnramifiedOperatorFamily

section ActualCharacters

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)

section Composition

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {Ω₀ Ω₁ Ω₂ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

include hp hL in
/-- A composition identity on a nonempty open set holds for the continued
families at every parameter regular for all three continuations. -/
theorem RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition
    {A : Ω₀ → V →ₗ[ℂ] W} {B : Ω₁ → W →ₗ[ℂ] Z} {C : Ω₂ → V →ₗ[ℂ] Z}
    (p : RationalOperatorContinuationData Ω₀ A)
    (q : RationalOperatorContinuationData Ω₁ B)
    (r : RationalOperatorContinuationData Ω₂ C) (h : HasOpenComposition A B C)
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (h₀ : χ ∈ p.regularRegion) (h₁ : χ ∈ q.regularRegion) (h₂ : χ ∈ r.regularRegion) :
    r.continuedOperator ⟨χ, h₂⟩ =
      (q.continuedOperator ⟨χ, h₁⟩).comp (p.continuedOperator ⟨χ, h₀⟩) := by
  obtain ⟨D, hD, hne, hD₀, hD₁, hD₂, he⟩ := h
  exact RationalOperatorContinuationData.continuedOperator_comp_of_eqOn L hp hL p q r
    hD hne hD₀ hD₁ hD₂ he ⟨χ, ⟨h₀, h₁⟩, h₂⟩

end Composition

section Parabolic

variable {X₀ : Type u₀} {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃}
  [AddCommGroup X₀] [Module ℂ X₀] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
  {Ω₁₀ Ω₀₂ Ω₂₃ Ω₃₁ Ω₁₂ Ω₂₁ Ω₀₃ Ω₃₀ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A₁₀ : Ω₁₀ → X₀ →ₗ[ℂ] X₁} {A₀₂ : Ω₀₂ → X₂ →ₗ[ℂ] X₀}
  {A₂₃ : Ω₂₃ → X₃ →ₗ[ℂ] X₂} {A₃₁ : Ω₃₁ → X₁ →ₗ[ℂ] X₃}
  {A₁₂ : Ω₁₂ → X₂ →ₗ[ℂ] X₁} {A₂₁ : Ω₂₁ → X₁ →ₗ[ℂ] X₂}
  {A₀₃ : Ω₀₃ → X₃ →ₗ[ℂ] X₀} {A₃₀ : Ω₃₀ → X₀ →ₗ[ℂ] X₃}
  (p₁₀ : RationalOperatorContinuationData Ω₁₀ A₁₀)
  (p₀₂ : RationalOperatorContinuationData Ω₀₂ A₀₂)
  (p₂₃ : RationalOperatorContinuationData Ω₂₃ A₂₃)
  (p₃₁ : RationalOperatorContinuationData Ω₃₁ A₃₁)
  (p₁₂ : RationalOperatorContinuationData Ω₁₂ A₁₂)
  (p₂₁ : RationalOperatorContinuationData Ω₂₁ A₂₁)
  (p₀₃ : RationalOperatorContinuationData Ω₀₃ A₀₃)
  (p₃₀ : RationalOperatorContinuationData Ω₃₀ A₃₀)

/-- The parameters regular for all eight continuations. -/
def parabolicRegularRegion :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)) :=
  p₁₀.regularRegion ∩ (p₀₂.regularRegion ∩ (p₂₃.regularRegion ∩ (p₃₁.regularRegion ∩
    (p₁₂.regularRegion ∩ (p₂₁.regularRegion ∩ (p₀₃.regularRegion ∩ p₃₀.regularRegion))))))

/-- The common regular region of eight continuations is open. -/
theorem parabolicRegularRegion_isOpen :
    IsOpen (parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀) :=
  p₁₀.regularRegion_isOpen.inter (p₀₂.regularRegion_isOpen.inter
    (p₂₃.regularRegion_isOpen.inter (p₃₁.regularRegion_isOpen.inter
      (p₁₂.regularRegion_isOpen.inter (p₂₁.regularRegion_isOpen.inter
        (p₀₃.regularRegion_isOpen.inter p₃₀.regularRegion_isOpen))))))

variable
  (h₁₂ : HasOpenComposition A₀₂ A₁₀ A₁₂) (h₂₁ : HasOpenComposition A₃₁ A₂₃ A₂₁)
  (h₀₃ : HasOpenComposition A₂₃ A₀₂ A₀₃) (h₃₀ : HasOpenComposition A₁₀ A₃₁ A₃₀)

/-- The eight continued families on their common regular region, with the four
composition identities extended from the given open sets. -/
def continuedParabolicCompositionData :
    ParabolicCompositionData (parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀)
      X₀ X₁ X₂ X₃ where
  J₁₀ χ := p₁₀.continuedOperator ⟨χ.val, χ.property.1⟩
  J₀₂ χ := p₀₂.continuedOperator ⟨χ.val, χ.property.2.1⟩
  J₂₃ χ := p₂₃.continuedOperator ⟨χ.val, χ.property.2.2.1⟩
  J₃₁ χ := p₃₁.continuedOperator ⟨χ.val, χ.property.2.2.2.1⟩
  J₁₂ χ := p₁₂.continuedOperator ⟨χ.val, χ.property.2.2.2.2.1⟩
  J₂₁ χ := p₂₁.continuedOperator ⟨χ.val, χ.property.2.2.2.2.2.1⟩
  J₀₃ χ := p₀₃.continuedOperator ⟨χ.val, χ.property.2.2.2.2.2.2.1⟩
  J₃₀ χ := p₃₀.continuedOperator ⟨χ.val, χ.property.2.2.2.2.2.2.2⟩
  comp₁₂ χ := RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition
    L hp hL p₀₂ p₁₀ p₁₂ h₁₂ χ.val _ _ _
  comp₂₁ χ := RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition
    L hp hL p₃₁ p₂₃ p₂₁ h₂₁ χ.val _ _ _
  comp₀₃ χ := RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition
    L hp hL p₂₃ p₀₂ p₀₃ h₀₃ χ.val _ _ _
  comp₃₀ χ := RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition
    L hp hL p₁₀ p₃₁ p₃₀ h₃₀ χ.val _ _ _

include p₁₀ p₀₂ p₂₃ p₃₁ h₁₂ h₂₁ h₀₃ h₃₀

/-- If the continued opposite composite for `P` is a nonzero rational scalar
and the continued opposite composite for `P'` is also scalar, the two
function-field scalars agree. Nonvanishing of the continued `J_{P'|P}` is not
assumed: it follows from the composition `J_{P̄|P} = J_{P̄|P'} J_{P'|P}`. -/
theorem continuedCompositeRationalScalar_eq_of_parabolicComposition
    (hΩ₃₀ : Ω₃₀.Nonempty) (hΩ₀₃ : Ω₀₃.Nonempty)
    (hΩ₂₁ : Ω₂₁.Nonempty) (hΩ₁₂ : Ω₁₂.Nonempty)
    (v : X₀) (ℓ : X₀ →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) (w : X₁) (m : X₁ →ₗ[ℂ] ℂ)
    (hsc : ∀ χ : ↥(p₃₀.regularRegion ∩ p₀₃.regularRegion),
      p₃₀.continuedComposite p₀₃ χ =
        p₃₀.continuedCompositeScalar p₀₃ v ℓ χ • LinearMap.id)
    (hsc' : ∀ χ : ↥(p₂₁.regularRegion ∩ p₁₂.regularRegion),
      p₂₁.continuedComposite p₁₂ χ =
        p₂₁.continuedCompositeScalar p₁₂ w m χ • LinearMap.id)
    (hne : continuedCompositeRationalScalar L hp hL p₃₀ p₀₃ hΩ₃₀ hΩ₀₃ v ℓ ≠ 0) :
    continuedCompositeRationalScalar L hp hL p₂₁ p₁₂ hΩ₂₁ hΩ₁₂ w m =
      continuedCompositeRationalScalar L hp hL p₃₀ p₀₃ hΩ₃₀ hΩ₀₃ v ℓ := by
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  obtain ⟨a, b, -, hbR, hs, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p₃₀ p₀₃ hΩ₃₀ hΩ₀₃ v ℓ
  obtain ⟨a', b', -, hbR', hs', hval'⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p₂₁ p₁₂ hΩ₂₁ hΩ₁₂ w m
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne
    rw [hs, map_zero, zero_div]
  let d := continuedParabolicCompositionData L hp hL
    p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀ h₁₂ h₂₁ h₀₃ h₃₀
  have hb : ∀ χ : ↥(parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀),
      b.val χ.val ≠ 0 := fun χ =>
    hbR ⟨χ.val, χ.property.2.2.2.2.2.2.2, χ.property.2.2.2.2.2.2.1⟩
  have hb' : ∀ χ : ↥(parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀),
      b'.val χ.val ≠ 0 := fun χ =>
    hbR' ⟨χ.val, χ.property.2.2.2.2.2.1, χ.property.2.2.2.2.1⟩
  have hc : ∀ χ : ↥(parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀),
      (d.J₀₃ χ).comp (d.J₃₀ χ) = (a.val χ.val / b.val χ.val) • LinearMap.id := fun χ =>
    (hsc ⟨χ.val, χ.property.2.2.2.2.2.2.2, χ.property.2.2.2.2.2.2.1⟩).trans
      (congrArg (fun c : ℂ => c • (LinearMap.id : X₀ →ₗ[ℂ] X₀)) (hval _))
  have hc' : ∀ χ : ↥(parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀),
      (d.J₁₂ χ).comp (d.J₂₁ χ) = (a'.val χ.val / b'.val χ.val) • LinearMap.id := fun χ =>
    (hsc' ⟨χ.val, χ.property.2.2.2.2.2.1, χ.property.2.2.2.2.1⟩).trans
      (congrArg (fun c : ℂ => c • (LinearMap.id : X₁ →ₗ[ℂ] X₁)) (hval' _))
  have hg : a * (p₁₀.denominator * (p₀₂.denominator * (p₂₃.denominator *
      (p₃₁.denominator * (p₁₂.denominator * (p₂₁.denominator *
        (p₀₃.denominator * p₃₀.denominator))))))) ≠ 0 :=
    mul_ne_zero ha (mul_ne_zero (p₁₀.denominator_ne_zero h₃₀.nonempty_first)
      (mul_ne_zero (p₀₂.denominator_ne_zero h₀₃.nonempty_second)
        (mul_ne_zero (p₂₃.denominator_ne_zero h₀₃.nonempty_first)
          (mul_ne_zero (p₃₁.denominator_ne_zero h₃₀.nonempty_second)
            (mul_ne_zero (p₁₂.denominator_ne_zero hΩ₁₂)
              (mul_ne_zero (p₂₁.denominator_ne_zero hΩ₂₁)
                (mul_ne_zero (p₀₃.denominator_ne_zero hΩ₀₃)
                  (p₃₀.denominator_ne_zero hΩ₃₀))))))))
  obtain ⟨χ, hχ⟩ := (rationalUnramifiedRegular_dense_nonzero L hp hL _ hg).nonempty
  simp only [Set.mem_ofPred_eq, Subalgebra.coe_mul, Pi.mul_apply, ne_eq, mul_eq_zero,
    not_or] at hχ
  let χ₀ : ↥(parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀) :=
    ⟨χ, hχ.2.1, hχ.2.2.1, hχ.2.2.2.1, hχ.2.2.2.2.1, hχ.2.2.2.2.2.1,
      hχ.2.2.2.2.2.2.1, hχ.2.2.2.2.2.2.2.1, hχ.2.2.2.2.2.2.2.2⟩
  have hχ₀ : d.J₁₀ χ₀ ≠ 0 := by
    intro h0
    have h30 : d.J₃₀ χ₀ = 0 := by
      rw [d.comp₃₀, h0, LinearMap.comp_zero]
    have hcomp := hc χ₀
    rw [h30, LinearMap.comp_zero] at hcomp
    have hv := congrArg (fun T : X₀ →ₗ[ℂ] X₀ => ℓ (T v)) hcomp
    simp only [LinearMap.zero_apply, map_zero, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul, hℓ, smul_eq_mul, mul_one] at hv
    exact div_ne_zero hχ.1 (hb χ₀) hv.symm
  have hJ : IsRationalOperatorOn (parabolicRegularRegion L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀)
      d.J₁₀ :=
    p₁₀.continuedOperator_rational.restrict fun _ hχ => hχ.1
  exact Langlands.Plancherel.ParabolicCompositionData.functionField_eq L hp hL d
    (parabolicRegularRegion_isOpen L p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀)
    hJ χ₀ hχ₀ _ _ a b a' b' hb hb' hs hs' hc hc'

/-- Symmetric form. With the four further families from `P'` to `P`, from `P̄`
to `P'`, from `P̄'` to `P̄` and from `P` to `P̄'`, and the four composition
identities with the roles of `P` and `P'` exchanged, the two continued
opposite scalars agree without any nonvanishing hypothesis. -/
theorem continuedCompositeRationalScalar_eq_of_parabolicComposition_symm
    {Ω₀₁ Ω₁₃ Ω₃₂ Ω₂₀ :
      Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    {A₀₁ : Ω₀₁ → X₁ →ₗ[ℂ] X₀} {A₁₃ : Ω₁₃ → X₃ →ₗ[ℂ] X₁}
    {A₃₂ : Ω₃₂ → X₂ →ₗ[ℂ] X₃} {A₂₀ : Ω₂₀ → X₀ →ₗ[ℂ] X₂}
    (p₀₁ : RationalOperatorContinuationData Ω₀₁ A₀₁)
    (p₁₃ : RationalOperatorContinuationData Ω₁₃ A₁₃)
    (p₃₂ : RationalOperatorContinuationData Ω₃₂ A₃₂)
    (p₂₀ : RationalOperatorContinuationData Ω₂₀ A₂₀)
    (h₀₃' : HasOpenComposition A₁₃ A₀₁ A₀₃) (h₃₀' : HasOpenComposition A₂₀ A₃₂ A₃₀)
    (h₁₂' : HasOpenComposition A₃₂ A₁₃ A₁₂) (h₂₁' : HasOpenComposition A₀₁ A₂₀ A₂₁)
    (hΩ₃₀ : Ω₃₀.Nonempty) (hΩ₀₃ : Ω₀₃.Nonempty)
    (hΩ₂₁ : Ω₂₁.Nonempty) (hΩ₁₂ : Ω₁₂.Nonempty)
    (v : X₀) (ℓ : X₀ →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) (w : X₁) (m : X₁ →ₗ[ℂ] ℂ) (hm : m w = 1)
    (hsc : ∀ χ : ↥(p₃₀.regularRegion ∩ p₀₃.regularRegion),
      p₃₀.continuedComposite p₀₃ χ =
        p₃₀.continuedCompositeScalar p₀₃ v ℓ χ • LinearMap.id)
    (hsc' : ∀ χ : ↥(p₂₁.regularRegion ∩ p₁₂.regularRegion),
      p₂₁.continuedComposite p₁₂ χ =
        p₂₁.continuedCompositeScalar p₁₂ w m χ • LinearMap.id) :
    continuedCompositeRationalScalar L hp hL p₂₁ p₁₂ hΩ₂₁ hΩ₁₂ w m =
      continuedCompositeRationalScalar L hp hL p₃₀ p₀₃ hΩ₃₀ hΩ₀₃ v ℓ := by
  by_cases h : continuedCompositeRationalScalar L hp hL p₃₀ p₀₃ hΩ₃₀ hΩ₀₃ v ℓ = 0
  · by_cases h' : continuedCompositeRationalScalar L hp hL p₂₁ p₁₂ hΩ₂₁ hΩ₁₂ w m = 0
    · rw [h, h']
    · exact (continuedCompositeRationalScalar_eq_of_parabolicComposition L hp hL
        p₀₁ p₁₃ p₃₂ p₂₀ p₀₃ p₃₀ p₁₂ p₂₁ h₀₃' h₃₀' h₁₂' h₂₁'
        hΩ₂₁ hΩ₁₂ hΩ₃₀ hΩ₀₃ w m hm v ℓ hsc' hsc h').symm
  · exact continuedCompositeRationalScalar_eq_of_parabolicComposition L hp hL
      p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀ h₁₂ h₂₁ h₀₃ h₃₀
      hΩ₃₀ hΩ₀₃ hΩ₂₁ hΩ₁₂ v ℓ hℓ w m hsc hsc' h

end Parabolic

end ActualCharacters

end Langlands.Plancherel
