import Langlands.Representation.Plancherel.CompactIntertwiningComposition
import Langlands.Representation.Plancherel.CompactIntertwiningContinuation

/-! # Composite rational continuations and continued composition identities -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

universe u uG uI uV uW uZ

namespace UnramifiedOperatorFamily

namespace RationalOperatorContinuationData

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {Ω₀ Ω₁ : Set (unramifiedCharacters ν)}
  {A : Ω₀ → V →ₗ[ℂ] W} {B : Ω₁ → W →ₗ[ℂ] Z}
  (p : RationalOperatorContinuationData Ω₀ A)
  (q : RationalOperatorContinuationData Ω₁ B)

/-- The composite of two continuations continues the composite family on the
intersection of the two original regions. Its denominator is the product of
the two given denominators and its numerator is the composite numerator. -/
def comp : RationalOperatorContinuationData (Ω₀ ∩ Ω₁)
    (fun χ => (B ⟨χ.val, χ.property.2⟩).comp (A ⟨χ.val, χ.property.1⟩)) where
  denominator := q.denominator * p.denominator
  denominator_nonzero χ := by
    simp only [Subalgebra.coe_mul, Pi.mul_apply]
    exact mul_ne_zero (q.denominator_nonzero ⟨χ.val, χ.property.2⟩)
      (p.denominator_nonzero ⟨χ.val, χ.property.1⟩)
  numerator χ := (q.numerator χ).comp (p.numerator χ)
  polynomial := q.polynomial.comp p.polynomial
  clears χ := by
    have hq := q.clears ⟨χ.val, χ.property.2⟩
    have hp := p.clears ⟨χ.val, χ.property.1⟩
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Subalgebra.coe_mul,
      Pi.mul_apply]
    rw [hq, hp]
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [mul_comm]

/-- A parameter is regular for the composite exactly when it is regular for
both factors. -/
theorem mem_comp_regularRegion (χ : unramifiedCharacters ν) :
    χ ∈ (p.comp q).regularRegion ↔ χ ∈ p.regularRegion ∧ χ ∈ q.regularRegion := by
  simp only [regularRegion, comp, Set.mem_ofPred_eq, Subalgebra.coe_mul,
    Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
  exact and_comm

theorem comp_regularRegion :
    (p.comp q).regularRegion = p.regularRegion ∩ q.regularRegion :=
  Set.ext (p.mem_comp_regularRegion q)

/-- The continued composite is the composite of the two continued families at
every common regular parameter. -/
theorem comp_continuedOperator (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    (p.comp q).continuedOperator ⟨χ.val, (p.mem_comp_regularRegion q χ.val).mpr χ.property⟩ =
      (q.continuedOperator ⟨χ.val, χ.property.2⟩).comp
        (p.continuedOperator ⟨χ.val, χ.property.1⟩) := by
  apply LinearMap.ext
  intro v
  simp only [continuedOperator, comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, smul_smul, Subalgebra.coe_mul, Pi.mul_apply, mul_inv]
  rw [mul_comm]

end RationalOperatorContinuationData

end UnramifiedOperatorFamily

section ActualCharacters

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  {Ω₀ Ω₁ Ω₂ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]

include hp hG in
/-- A composition identity of three original families on one nonempty open
subset of their regions extends to their continuations, at every parameter
regular for all three. The three original regions need not be open. -/
theorem RationalOperatorContinuationData.continuedOperator_comp_of_eqOn
    {A : Ω₀ → V →ₗ[ℂ] W} {B : Ω₁ → W →ₗ[ℂ] Z} {C : Ω₂ → V →ₗ[ℂ] Z}
    (p : RationalOperatorContinuationData Ω₀ A)
    (q : RationalOperatorContinuationData Ω₁ B)
    (r : RationalOperatorContinuationData Ω₂ C)
    (hD : IsOpen D) (hne : D.Nonempty)
    (hD₀ : D ⊆ Ω₀) (hD₁ : D ⊆ Ω₁) (hD₂ : D ⊆ Ω₂)
    (he : ∀ χ (hχ : χ ∈ D),
      C ⟨χ, hD₂ hχ⟩ = (B ⟨χ, hD₁ hχ⟩).comp (A ⟨χ, hD₀ hχ⟩)) :
    ∀ χ : ↥(p.regularRegion ∩ q.regularRegion ∩ r.regularRegion),
      r.continuedOperator ⟨χ.val, χ.property.2⟩ =
        (q.continuedOperator ⟨χ.val, χ.property.1.2⟩).comp
          (p.continuedOperator ⟨χ.val, χ.property.1.1⟩) := by
  have hDR : D ⊆ p.regularRegion ∩ q.regularRegion ∩ r.regularRegion :=
    fun χ hχ => ⟨⟨p.subset_regularRegion (hD₀ hχ), q.subset_regularRegion (hD₁ hχ)⟩,
      r.subset_regularRegion (hD₂ hχ)⟩
  refine rationalUnramifiedOperator_eq_of_eqOn_isOpen G hp hG hD hne hDR
    (fun χ => r.continuedOperator ⟨χ.val, χ.property.2⟩)
    (fun χ => (q.continuedOperator ⟨χ.val, χ.property.1.2⟩).comp
      (p.continuedOperator ⟨χ.val, χ.property.1.1⟩))
    (r.continuedOperator_rational.restrict fun _ hχ => hχ.2)
    ((q.continuedOperator_rational.restrict fun _ hχ => hχ.1.2).comp
      (p.continuedOperator_rational.restrict fun _ hχ => hχ.1.1)) ?_
  intro χ hχ
  have hr := r.continuedOperator_agrees ⟨χ, hD₂ hχ⟩
  have hq := q.continuedOperator_agrees ⟨χ, hD₁ hχ⟩
  have hp' := p.continuedOperator_agrees ⟨χ, hD₀ hχ⟩
  exact hr.trans ((he χ hχ).trans (by rw [← hq, ← hp']))

end ActualCharacters

section ActualIntertwiners

open Aubert.General Induction UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ P₂ M U₀ U₁ U₂ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (h₂ : IsSemidirectDecomposition P₂ M U₂) (hU₂ : IsClosed (U₂ : Set G))
  (hδ₂ : IsUnimodularModulus U₂ hU₂)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₂ : IsClosed (P₂ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hP₂K : ∀ g : G, ∃ p : P₂, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (hr₂ : Continuous h₂.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {Ω₁₀ Ω₂₁ Ω₂₀ D₁₀ D₂₁ D₂₀ D :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)

variable
  (J₁₀ : ∀ χ : Ω₁₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (J₂₁ : ∀ χ : Ω₂₁,
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (J₂₀ : ∀ χ : Ω₂₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (p₁₀ : RationalOperatorContinuationData Ω₁₀ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₁₀ χ)))
  (p₂₁ : RationalOperatorContinuationData Ω₂₁ (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₂₁ χ)))
  (p₂₀ : RationalOperatorContinuationData Ω₂₀ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₂₀ χ)))
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty) (hD₁₀Ω : D₁₀ ⊆ Ω₁₀)
  (hD₂₁ : IsOpen D₂₁) (hne₂₁ : D₂₁.Nonempty) (hD₂₁Ω : D₂₁ ⊆ Ω₂₁)
  (hD₂₀ : IsOpen D₂₀) (hne₂₀ : D₂₀.Nonempty) (hD₂₀Ω : D₂₀ ⊆ Ω₂₀)

/-- Continued actual ambient intertwiners compose at every parameter regular
for all three continuations, once the original actual families compose on one
nonempty open subset of their three regions. -/
theorem continuedInductionIntertwiner_comp_of_eqOn
    (hD : IsOpen D) (hne : D.Nonempty)
    (hD₁₀' : D ⊆ Ω₁₀) (hD₂₁' : D ⊆ Ω₂₁) (hD₂₀' : D ⊆ Ω₂₀)
    (he : ∀ χ (hχ : χ ∈ D),
      J₂₀ ⟨χ, hD₂₀' hχ⟩ = (J₂₁ ⟨χ, hD₂₁' hχ⟩).comp (J₁₀ ⟨χ, hD₁₀' hχ⟩))
    (χ : ↥(p₁₀.regularRegion ∩ p₂₁.regularRegion ∩ p₂₀.regularRegion)) :
    continuedInductionIntertwiner L hp hL h₀ hU₀ hδ₀ h₂ hU₂ hδ₂ K hK
        hP₀ hP₂ hP₀K hP₂K hr₀ hr₂ e hν A J₂₀ p₂₀ hD₂₀ hne₂₀ hD₂₀Ω
        ⟨χ.val, χ.property.2⟩ =
      (continuedInductionIntertwiner L hp hL h₁ hU₁ hδ₁ h₂ hU₂ hδ₂ K hK
          hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ e hν A J₂₁ p₂₁ hD₂₁ hne₂₁ hD₂₁Ω
          ⟨χ.val, χ.property.1.2⟩).comp
        (continuedInductionIntertwiner L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
          hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J₁₀ p₁₀ hD₁₀ hne₁₀ hD₁₀Ω
          ⟨χ.val, χ.property.1.1⟩) := by
  have h := RationalOperatorContinuationData.continuedOperator_comp_of_eqOn L hp hL
    p₁₀ p₂₁ p₂₀ hD hne hD₁₀' hD₂₁' hD₂₀' (by
      intro ψ hψ
      rw [he ψ hψ]
      exact compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁
        hP₀K hP₁K hr₀ hr₁ νM hνM (χM ψ) A h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ _ _) χ
  have h₂₀ := continuedInductionIntertwiner_compact L hp hL h₀ hU₀ hδ₀ h₂ hU₂ hδ₂ K hK
    hP₀ hP₂ hP₀K hP₂K hr₀ hr₂ e hν A J₂₀ p₂₀ hD₂₀ hne₂₀ hD₂₀Ω ⟨χ.val, χ.property.2⟩
  have h₂₁ := continuedInductionIntertwiner_compact L hp hL h₁ hU₁ hδ₁ h₂ hU₂ hδ₂ K hK
    hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ e hν A J₂₁ p₂₁ hD₂₁ hne₂₁ hD₂₁Ω ⟨χ.val, χ.property.1.2⟩
  have h₁₀ := continuedInductionIntertwiner_compact L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A J₁₀ p₁₀ hD₁₀ hne₁₀ hD₁₀Ω ⟨χ.val, χ.property.1.1⟩
  exact (compactIntertwiningOperator_comp_eq_iff h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁
    hP₀K hP₁K hr₀ hr₁ νM hνM (χM χ.val) A h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ _ _ _).mp
    (h₂₀.trans (h.trans (congrArg₂ (fun a b => LinearMap.comp a b) h₂₁.symm h₁₀.symm)))

end ActualIntertwiners

end Langlands.Plancherel
