import Langlands.LocalFactor.BrauerKernel.Determinant
import Langlands.LocalFactor.Abelian.UnramifiedTwist
import Langlands.ClassFieldTheory.Local.NormOrderProof

/-! # Brauer relations among unramified twists over unramified extensions -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The chosen uniformizer of `E`, mapped into a larger field. -/
abbrev baseUniformizer (E L : Extension F) (h : E.field ≤ L.field) : L.fieldˣ :=
  E.unitsInclusion L h (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E))

/-- If `L/E` has the same absolute ramification index, the uniformizer of `E` is a
uniformizer of `L`. -/
theorem ord_baseUniformizer (E L : Extension F) (h : E.field ≤ L.field)
    (hram : (fieldData F L).ramificationIndex = (fieldData F E).ramificationIndex) :
    (fieldData F L).ord ((baseUniformizer F E L h : L.fieldˣ) : L.field) = 1 := by
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  have : IsScalarTower (Padic p) E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.field L.field := FiniteDimensional.right F.Carrier E.field L.field
  have key := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap
    (E.asPadicField (p := p)) (L.asPadicField (p := p)) (fieldData F E) (fieldData F L)
    (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E) : E.field)
  rw [hram, LocalFactor.PadicAbelian.uniformizerUnit_ord, mul_one] at key
  have hpos : ((fieldData F E).ramificationIndex : ℤ) ≠ 0 := by
    exact_mod_cast (fieldData F E).ramificationIndex_pos.ne'
  have key' := mul_left_cancel₀ hpos (key.trans (mul_one _).symm)
  exact key'

/-- The epsilon ratio of two unramified twists of one character, over a field with the
base absolute ramification index. -/
theorem generatorValue_of_unramifiedTwist {E : Extension F} (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (g : Generator F E)
    (hram : (fieldData F g.extension).ramificationIndex = (fieldData F E).ramificationIndex)
    (β χ₀ χ₀' : FieldCharacter F g.extension)
    (h₀ : (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀)
    (h₀' : (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀')
    (h₁ : g.first = χ₀ * β) (h₂ : g.second = χ₀' * β) :
    generatorValue F E ψ measures g =
      generatorCharacterRatio F E g (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E)) ^
        ((fieldData F g.extension).additiveConductor
            (traceCharacter F E g.extension g.inclusion ψ) +
          ((fieldData F g.extension).multiplicativeConductor β : ℤ)) := by
  let T := fieldData F g.extension
  let := T.topology
  let π := baseUniformizer F E g.extension g.inclusion
  have hπ : T.ord ((π : g.extension.fieldˣ) : g.extension.field) = 1 :=
    ord_baseUniformizer F E g.extension g.inclusion hram
  let ψL := traceCharacter F E g.extension g.inclusion ψ
  let N : ℤ := T.additiveConductor ψL + (T.multiplicativeConductor β : ℤ)
  have hfac (ω : FieldCharacter F g.extension) (hω : T.IsUnramifiedQuasicharacter ω) :
      T.abelianUnramifiedTwistFactor ω ψL (T.multiplicativeConductor β) = ω π ^ N :=
    T.abelianUnramifiedTwistFactor_eq_uniformizer ω hω ψL _ π hπ
  have hunit (ω : FieldCharacter F g.extension) (hω : T.IsUnramifiedQuasicharacter ω) :
      T.abelianEpsilonUnit (ω * β) ψL (measures g.extension) =
        ω π ^ N * T.abelianEpsilonUnit β ψL (measures g.extension) := by
    apply Units.ext
    rw [Units.val_mul, PadicField.TopologicalData.coe_abelianEpsilonUnit,
      PadicField.TopologicalData.coe_abelianEpsilonUnit, mul_comm ω β,
      T.abelianEpsilonExpression_mul_unramified β ω hω, hfac ω hω]
  change T.abelianEpsilonUnit g.first ψL (measures g.extension) /
      T.abelianEpsilonUnit g.second ψL (measures g.extension) = _
  rw [h₁, h₂, hunit χ₀ h₀, hunit χ₀' h₀', mul_div_mul_right_eq_div, ← div_zpow]
  congr 1
  rw [generatorCharacterRatio, h₁, h₂]
  change χ₀ π / χ₀' π = (χ₀ * β) π / (χ₀' * β) π
  rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.mul_apply, mul_div_mul_right_eq_div]

/-- **Unramified Brauer relations.** Suppose every generator of an actual relation lies
over a field with the base absolute ramification index, and has as characters two
unramified twists of a common character, with the same exponent
`n(ψ ∘ Tr) + a(β) = N` for every generator. Then the abelian epsilon evaluation of the
relation is trivial. -/
theorem evaluationMap_eq_zero_of_unramifiedTwist (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) (N : ℤ)
    (hgen : ∀ g ∈ z.support,
      (fieldData F g.extension).ramificationIndex = (fieldData F E).ramificationIndex ∧
      ∃ β χ₀ χ₀' : FieldCharacter F g.extension,
        (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀ ∧
        (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀' ∧
        g.first = χ₀ * β ∧ g.second = χ₀' * β ∧
        (fieldData F g.extension).additiveConductor
            (traceCharacter F E g.extension g.inclusion ψ) +
          ((fieldData F g.extension).multiplicativeConductor β : ℤ) = N) :
    evaluationMap F E ψ measures z = 0 := by
  have hval : ∀ g ∈ z.support, generatorValue F E ψ measures g =
      generatorCharacterRatio F E g
        (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E)) ^ N := by
    intro g hg
    obtain ⟨hram, β, χ₀, χ₀', h₀, h₀', h₁, h₂, hN⟩ := hgen g hg
    rw [generatorValue_of_unramifiedTwist F ψ measures g hram β χ₀ χ₀' h₀ h₀' h₁ h₂, hN]
  have hrat := characterRatioMap_eq_zero.{uF, uV} F e he E z hz
    (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E))
  have heval : evaluationMap F E ψ measures z =
      N • characterRatioMap F E
        (LocalFactor.PadicAbelian.uniformizerUnit (fieldData F E)) z := by
    rw [evaluationMap, characterRatioMap, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    refine (Finset.sum_congr rfl fun g hg => ?_).trans (Finset.sum_zsmul _ _ N)
    rw [hval g hg, ofMul_zpow, smul_comm]
  rw [heval, hrat, smul_zero]

end Langlands.LocalFactor.NonabelianBrauer
