import Langlands.Representation.RankinSelberg.ModelAsymptoticStatement
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.LocalField.Normalization.Proof

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

private theorem character_sum_eq_product {F : Type uF} [Field F]
    [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (f : Fin n → F) : ψ.complex (∑ i, f i) = ∏ i, ψ.complex (f i) := by
  have h (s : Finset (Fin n)) :
      ψ.complex (∑ i ∈ s, f i) = ∏ i ∈ s, ψ.complex (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]
  exact h Finset.univ

private theorem functional_equivariant_iff {F : Type uF} [Field F]
    [TopologicalSpace F] {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ψ : UnitaryAdditiveCharacter F) (ℓ : Module.Dual ℂ V) :
    ℓ ∈ glFunctionals ψ n π ↔
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (π g v) = (∏ i : Fin n, ψ.complex (g.val i.castSucc i.succ)) * ℓ v := by
  constructor
  · intro h g hg v
    have he := h ⟨g, hg⟩ v
    simpa only [standardCharacter_apply, character_sum_eq_product] using he
  · intro h u v
    simpa only [standardCharacter_apply, character_sum_eq_product] using h u.val u.property v

private theorem coefficientTorusExpansion_standard
    (h : WhittakerTypeAsymptoticStatement.{uF, uV})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      IsOfWhittakerType n (standardCharacter ψ n) π →
      CoefficientTorusExpansion (standardCharacter ψ n) π := by
  let := F.canonicalTopologicalData.topology
  intro n V _ _ π ψ hπ
  obtain ⟨e⟩ := hπ.2.2
  let ℓ₀ : glFunctionals ψ n π := e.symm 1
  have hℓ₀ : ℓ₀.val ≠ 0 := by
    intro hz
    have hz' : ℓ₀ = 0 := Subtype.ext hz
    have he := congrArg e hz'
    simp [ℓ₀] at he
  have hψ : ψ.complex ≠ 1 := by
    intro hz
    apply ψ.nontrivial
    ext x
    exact DFunLike.congr_fun hz x
  have huniq (ℓ : Module.Dual ℂ V) (hℓ : ℓ ∈ glFunctionals ψ n π) :
      ∃ c : ℂ, ℓ = c • ℓ₀.val := by
    refine ⟨e ⟨ℓ, hℓ⟩, ?_⟩
    have he : (⟨ℓ, hℓ⟩ : glFunctionals ψ n π) = e ⟨ℓ, hℓ⟩ • ℓ₀ := by
      apply e.injective
      simp [ℓ₀]
    exact congrArg Subtype.val he
  obtain ⟨X, hX, hExp⟩ := h p inferInstance F n V π ψ.complex
    ψ.continuous_complex hψ ψ.norm_complex hπ.1 hπ.2.1
    ⟨ℓ₀.val, hℓ₀, (functional_equivariant_iff π ψ ℓ₀.val).mp ℓ₀.property,
      fun ℓ hℓ => huniq ℓ ((functional_equivariant_iff π ψ ℓ).mpr hℓ)⟩
  refine ⟨X, hX, ?_⟩
  intro ℓ W
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ W
  obtain ⟨φ, hφ⟩ := hExp ℓ.val ((functional_equivariant_iff π ψ ℓ.val).mp ℓ.property) v
  refine ⟨φ, ?_⟩
  intro a
  exact hφ a

/-- Transport the assumed canonical expansion to the actual coefficient models,
for any supplied field topology and either standard character sign. -/
theorem modelAsymptoticTransfer : ModelAsymptoticTransferStatement.{uF, uV} := by
  intro h p hp F T
  have hT : T.topology = F.canonicalTopologicalData.topology :=
    T.topology_eq_canonicalModule.trans
      F.canonicalTopologicalData.topology_eq_canonicalModule.symm
  rw [hT]
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro n V _ _ π ψ θ hθ hπ
  rcases hθ with rfl | rfl
  · exact coefficientTorusExpansion_standard h F n V π ψ hπ
  · have hπ' : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n) π := by
      simpa only [standardCharacter_scale_neg_one] using hπ
    simpa only [standardCharacter_scale_neg_one] using
      coefficientTorusExpansion_standard h F n V π (ψ.scale (-1)) hπ'

end Langlands.RankinSelberg
