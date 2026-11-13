import Langlands.LocalFactor.BrauerKernel.StandaloneBridge
import Langlands.LocalFactor.CommonClosureSpectralGenerationReduction

/-! # Tate epsilon products of standalone Brauer relations -/

noncomputable section

set_option autoImplicit false

universe u w

namespace Langlands.LocalFactor.NonabelianBrauer

open VirtualRepresentation CommonClosure Weil.Local Correspondence LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Every p-adic field carries its canonical topology in this file. -/
local instance standaloneEpsilonTopology (E : PadicField.{u} p) : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology

/-- Every p-adic field carries its Borel σ-algebra in this file. -/
local instance standaloneEpsilonMeasurable (E : PadicField.{u} p) : MeasurableSpace E.Carrier :=
  borel E.Carrier

/-- If the evaluation of a combination of standalone generators vanishes, the product of the
Tate epsilon ratios `ε(η_j, ψF ∘ Tr, μ_j, 0) / ε(η'_j, ψF ∘ Tr, μ_j, 0)` raised to `n_j` is `1`,
for every choice of Haar measures `μ_j`. -/
theorem prod_epsilon_ratio_eq_one_of_evaluationMap (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier) (η η' : ∀ j, QuasiCharacter (E j))
    (n : J → ℤ) (ψF : NontrivialAdditiveCharacter F)
    (ψ : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψF ψ)
    (measures : HaarFamily F)
    (h0 : evaluationMap F (baseExtension F) ψ measures
      (∑ j, n j • Finsupp.single (standaloneGenerator F e (E j) (g j) (η j) (η' j)) 1) = 0)
    (μ : ∀ j, LocalAdditiveHaarMeasure (E j)) :
    ∏ j, (PadicAbelian.epsilon (E j).canonicalTopologicalData (η j)
          (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0 /
        PadicAbelian.epsilon (E j).canonicalTopologicalData (η' j)
          (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0) ^ n j =
      1 := by
  have h1 := (evaluationMap_imageGenerator F e E g _ _ n ψ measures).symm.trans h0
  have h2 : ∏ j, generatorValue F (baseExtension F) ψ measures
      (standaloneGenerator F e (E j) (g j) (η j) (η' j)) ^ n j = 1 := by
    have h3 := congrArg Additive.toMul h1
    rw [toMul_sum] at h3
    simp only [toMul_zsmul, toMul_ofMul, toMul_zero] at h3
    exact h3
  have h4 := congrArg (fun x : ℂˣ => (x : ℂ)) h2
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h4
  rw [← h4]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [generatorValue_standaloneGenerator F (E j) (g j) e he (η j) (η' j) ψF ψ hψ measures (μ j)]

/-- A family of Haar measures on the finite intermediate fields of the common closure. -/
def standaloneEpsilonMeasures : HaarFamily F :=
  fun L => Classical.choice (CommonClosureSpectralAnalytic.haarMeasure_nonempty L)

/-- **Tate epsilon products of unramified standalone relations.** Let the standalone
extensions `E_j / F` have the ramification index of `F`, and let `η_j = η₀_j · (α ∘ N)`,
`η'_j = η₀'_j · (α ∘ N)` with `η₀_j`, `η₀'_j` unramified and one quasicharacter `α` of `F`. If
`Σ_j n_j Ind_{E_j/F}([η_j ∘ rec] - [η'_j ∘ rec]) = 0`, then for every nontrivial additive
character `ψF` of `F` and all Haar measures `μ_j`,
`Π_j (ε(η_j, ψF ∘ Tr, μ_j, 0) / ε(η'_j, ψF ∘ Tr, μ_j, 0)) ^ n_j = 1`. -/
theorem prod_epsilon_ratio_eq_one_of_unramified (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier) (η η' : ∀ j, QuasiCharacter (E j))
    (n : J → ℤ)
    (h : ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (ExactGrothendieckGroup.characterClass.{u, w}
            (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e) (η j)) -
          ExactGrothendieckGroup.characterClass.{u, w}
            (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
              (η' j))) = 0)
    (α : QuasiCharacter F)
    (hgen : ∀ j, (E j).canonicalTopologicalData.ramificationIndex =
        F.canonicalTopologicalData.ramificationIndex ∧
      ∃ η₀ η₀' : QuasiCharacter (E j),
        (E j).canonicalTopologicalData.IsUnramifiedQuasicharacter η₀ ∧
        (E j).canonicalTopologicalData.IsUnramifiedQuasicharacter η₀' ∧
        (∀ x, η j x = η₀ x * α (Units.map
          (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
            x)) ∧
        (∀ x, η' j x = η₀' x * α (Units.map
          (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
            x)))
    (ψF : NontrivialAdditiveCharacter F) (μ : ∀ j, LocalAdditiveHaarMeasure (E j)) :
    ∏ j, (PadicAbelian.epsilon (E j).canonicalTopologicalData (η j)
          (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0 /
        PadicAbelian.epsilon (E j).canonicalTopologicalData (η' j)
          (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0) ^ n j =
      1 :=
  prod_epsilon_ratio_eq_one_of_evaluationMap F e he E g η η' n ψF
    (baseFieldAdditiveCharacterEquiv F ψF)
    ((isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψF _).mpr rfl)
    (standaloneEpsilonMeasures F)
    (evaluationMap_standalone_eq_zero_of_unramified.{u, w} F e he E g η η' n h α hgen _ _) μ

/-- **Tate epsilon products of ramified standalone relations.** Fix finitely many standalone
extensions `E_j / F`, a nontrivial additive character `ψF` of `F` and a conductor bound `K`.
There is `B` with the following property. Let `a(α) ≥ B`, and let `η_j = η₀_j · (α ∘ N)`,
`η'_j = η₀'_j · (α ∘ N)` with `a(η₀_j), a(η₀'_j) ≤ K`. If
`Σ_j n_j Ind_{E_j/F}([η_j ∘ rec] - [η'_j ∘ rec]) = 0`, then for all Haar measures `μ_j`,
`Π_j (ε(η_j, ψF ∘ Tr, μ_j, 0) / ε(η'_j, ψF ∘ Tr, μ_j, 0)) ^ n_j = 1`. -/
theorem exists_bound_prod_epsilon_ratio_eq_one_of_ramified (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier) (ψF : NontrivialAdditiveCharacter F)
    (K : ℕ) :
    ∃ B : ℕ, ∀ α : QuasiCharacter F, B ≤ F.canonicalTopologicalData.multiplicativeConductor α →
      ∀ (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ),
        ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong
            (extensionWeilMap F (E j) (g j)) (extensionWeilMap_isOpenEmbedding F (E j) (g j))
            (ExactGrothendieckGroup.characterClass.{u, w}
                (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
                  (η j)) -
              ExactGrothendieckGroup.characterClass.{u, w}
                (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
                  (η' j))) = 0 →
        (∀ j, ∃ η₀ η₀' : QuasiCharacter (E j),
          (E j).canonicalTopologicalData.multiplicativeConductor η₀ ≤ K ∧
          (E j).canonicalTopologicalData.multiplicativeConductor η₀' ≤ K ∧
          (∀ x, η j x = η₀ x * α (Units.map
            (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
              x)) ∧
          (∀ x, η' j x = η₀' x * α (Units.map
            (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
              x))) →
        ∀ μ : ∀ j, LocalAdditiveHaarMeasure (E j),
          ∏ j, (PadicAbelian.epsilon (E j).canonicalTopologicalData (η j)
                (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0 /
              PadicAbelian.epsilon (E j).canonicalTopologicalData (η' j)
                (SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF) (μ j).measure 0) ^
              n j = 1 := by
  obtain ⟨B, hB⟩ := exists_bound_evaluationMap_standalone_eq_zero_of_ramified.{u, w} F e he E g
    (baseFieldAdditiveCharacterEquiv F ψF) (standaloneEpsilonMeasures F) K
  exact ⟨B, fun α hα η η' n h hgen μ =>
    prod_epsilon_ratio_eq_one_of_evaluationMap F e he E g η η' n ψF
      (baseFieldAdditiveCharacterEquiv F ψF)
      ((isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψF _).mpr rfl)
      (standaloneEpsilonMeasures F) (hB α hα η η' n h hgen) μ⟩

end Langlands.LocalFactor.NonabelianBrauer
