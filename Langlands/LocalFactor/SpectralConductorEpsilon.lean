import Langlands.LocalFactor.CommonClosureSpectralGenerationReduction
import Langlands.LocalFactor.CommonClosureRankOneSpectral

/-!
# The epsilon side of Tate's spectral conductor formula

For a supplied local-constant system and a fixed spectral parameter `s`, the
spectral value of every continuous exact virtual class is the ordinary value
times `exp(-s (a(x) + n(ψ) deg x) log q)`, for any additive "logarithmic
conductor" `a` that vanishes on the trivial character and takes the value
`(c(χ) - c(χ')) log q_L` on each induced character difference. The proof is
the rank-one formula, the degree-zero induction law and degree-zero generation.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.SpectralConductor

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic
open VirtualRepresentation NonabelianSystem

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The complex logarithm of the residue cardinality of an intermediate field. -/
abbrev logCardinality (E : Extension F) : ℂ :=
  (Real.log ((fieldData F E).residueCardinality : ℝ) : ℂ)

/-- The multiplicative conductor of the field character attached to a
continuous Weil character by the supplied reciprocity component. -/
abbrev characterConductor (e : ReciprocityFamily F) (E : Extension F)
    (χ : weilSubgroup F E →ₜ* ℂˣ) : ℕ :=
  (fieldData F E).multiplicativeConductor (fieldCharacterEquiv F e E χ)

/-- The rank-one spectral formula of a supplied system at an intermediate field. -/
theorem value_virtualTwist_characterClass {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (χ : weilSubgroup F E →ₜ* ℂˣ)
    (s : ℂ) :
    (ε E ψ μ (virtualTwist F E s (ExactGrothendieckGroup.characterClass χ)) : ℂ) =
      ε E ψ μ (ExactGrothendieckGroup.characterClass χ) *
        Complex.exp (-s * ((((fieldData F E).additiveConductor ψ : ℂ) +
          (characterConductor e E χ : ℂ)) * logCardinality E)) := by
  change (ε E ψ μ (ExactGrothendieckGroup.continuousTwist (character F E s)
    (ExactGrothendieckGroup.characterClass χ)) : ℂ) = _
  rw [ExactGrothendieckGroup.continuousTwist_characterClass,
    value_characterClass F e E ε hε, value_characterClass F e E ε hε,
    abelianEpsilonExpression_of_isAbsTwist (fieldData F E)
      (fieldCharacterEquiv_isAbsTwist F e E hε.1 χ s) ψ μ]
  simp only [twistExponent, Int.cast_add, Int.cast_natCast]

/-- Additivity, in the form of a quotient of complex values. -/
theorem value_sub {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (x y : Virtual.{uF, uV} F E) :
    (ε E ψ μ (x - y) : ℂ) = ε E ψ μ x * (ε E ψ μ y : ℂ)⁻¹ := by
  have h := hε E ψ μ (x - y) y
  rw [sub_add_cancel] at h
  rw [eq_mul_inv_of_mul_eq h.symm, Units.val_mul, Units.val_inv_eq_inv_val]

/-- The spectral value of an induced character difference: the additive
conductors of the trace character cancel. -/
theorem value_virtualTwist_induce {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε) (E L : Extension F)
    (h : E.field ≤ L.field) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (χ χ' : weilSubgroup F L →ₜ* ℂˣ) (s : ℂ) :
    (ε E ψ μ (virtualTwist F E s (induce F E L h
        (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ'))) : ℂ) =
      ε E ψ μ (induce F E L h (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ')) *
        Complex.exp (-s * (((characterConductor e L χ : ℂ) -
          (characterConductor e L χ' : ℂ)) * logCardinality L)) := by
  obtain ⟨μL⟩ := haarMeasure_nonempty L
  set ψL := traceCharacter F E L h ψ
  have hdeg (z : ℂ) : degree F L (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ -
      ExactGrothendieckGroup.characterClass χ')) = 0 := by
    rw [degree_virtualTwist, map_sub, ExactGrothendieckGroup.degree_characterClass,
      ExactGrothendieckGroup.degree_characterClass, sub_self]
  have hind (z : ℂ) : ε E ψ μ (induce F E L h (virtualTwist F L z
      (ExactGrothendieckGroup.characterClass χ - ExactGrothendieckGroup.characterClass χ'))) =
      ε L ψL μL (virtualTwist F L z (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ')) :=
    hε.2.2.2.1 E L h ψ μ μL ⟨_, hdeg z⟩
  have h0 := hind 0
  simp only [virtualTwist_zero] at h0
  rw [virtualTwist_induce, hind s, h0, map_sub, value_sub hε.2.1, value_sub hε.2.1,
    value_virtualTwist_characterClass hε, value_virtualTwist_characterClass hε]
  have hX := Complex.exp_ne_zero (-s * ((((fieldData F L).additiveConductor ψL : ℂ) +
    (characterConductor e L χ' : ℂ)) * logCardinality L))
  calc _ = (ε L ψL μL (ExactGrothendieckGroup.characterClass χ) : ℂ) *
        (ε L ψL μL (ExactGrothendieckGroup.characterClass χ') : ℂ)⁻¹ *
        (Complex.exp (-s * ((((fieldData F L).additiveConductor ψL : ℂ) +
            (characterConductor e L χ : ℂ)) * logCardinality L)) *
          Complex.exp (-(-s * ((((fieldData F L).additiveConductor ψL : ℂ) +
            (characterConductor e L χ' : ℂ)) * logCardinality L)))) := by
        rw [Complex.exp_neg, mul_inv]
        ring
    _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        ring

/-- The trivial Weil character corresponds to an unramified field character. -/
theorem characterConductor_one (e : ReciprocityFamily F) (E : Extension F) :
    characterConductor e E (1 : weilSubgroup F E →ₜ* ℂˣ) = 0 := by
  rw [characterConductor, PadicField.TopologicalData.multiplicativeConductor_eq_zero_iff]
  intro u _
  obtain ⟨w, rfl⟩ := CommonClosure.reciprocityUnits_surjective F e E u
  have h := weilCharacter_fieldCharacterEquiv F e E (1 : weilSubgroup F E →ₜ* ℂˣ)
  exact DFunLike.congr_fun h w

/-- The spectral exponent of the right-hand side, additive in the class. -/
def spectralExponent (E : Extension F) (ψ : AdditiveCharacter F E)
    (a : Virtual.{uF, uV} F E →+ ℂ) : Virtual.{uF, uV} F E →+ ℂ where
  toFun x := a x + ((fieldData F E).additiveConductor ψ : ℂ) * (degree F E x : ℂ) *
    logCardinality E
  map_zero' := by
    rw [map_zero, show degree F E (0 : Virtual.{uF, uV} F E) = 0 from (degree F E).map_zero]
    simp
  map_add' x y := by
    simp only [map_add, Int.cast_add]
    ring

/-- The classes on which the spectral formula holds with exponent `a`. -/
def formulaSubgroup {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (s : ℂ) (a : Virtual.{uF, uV} F E →+ ℂ) :
    AddSubgroup (Virtual.{uF, uV} F E) where
  carrier := {x | (ε E ψ μ (virtualTwist F E s x) : ℂ) =
    ε E ψ μ x * Complex.exp (-s * spectralExponent E ψ a x)}
  zero_mem' := by
    simp [value_zero hε.2.1]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hε.2.1, hε.2.1, Units.val_mul, Units.val_mul, hx, hy, map_add, mul_add,
      Complex.exp_add]
    ring
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_neg, value_neg hε.2.1, value_neg hε.2.1, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, hx, map_neg, mul_neg, Complex.exp_neg, mul_inv]

/-- An induced character difference satisfies the formula as soon as `a` has the
rank-one value on it. -/
theorem induce_mem_formulaSubgroup {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (s : ℂ) (a : Virtual.{uF, uV} F E →+ ℂ)
    (L : Extension F) (h : E.field ≤ L.field) (χ χ' : weilSubgroup F L →ₜ* ℂˣ)
    (ha : a (induce F E L h (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ')) =
      ((characterConductor e L χ : ℂ) - (characterConductor e L χ' : ℂ)) *
        logCardinality L) :
    induce F E L h (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ') ∈ formulaSubgroup hε E ψ μ s a := by
  change _ = _
  rw [value_virtualTwist_induce hε E L h ψ μ χ χ' s]
  congr 2
  change _ = -s * (a _ + _)
  rw [ha, degree_induce, map_sub, ExactGrothendieckGroup.degree_characterClass,
    ExactGrothendieckGroup.degree_characterClass, sub_self, mul_zero]
  simp

/-- The trivial character satisfies the formula when `a` vanishes on it. -/
theorem one_mem_formulaSubgroup {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (s : ℂ) (a : Virtual.{uF, uV} F E →+ ℂ)
    (hone : a (ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ)) = 0) :
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      formulaSubgroup hε E ψ μ s a := by
  change _ = _
  rw [value_virtualTwist_characterClass hε, characterConductor_one]
  congr 2
  change _ = -s * (a _ + _)
  rw [hone, ExactGrothendieckGroup.degree_characterClass]
  simp

/-- Degree-zero generation, made finite: every class differs from its degree
times the trivial character by an integral combination of finitely many generators. -/
theorem exists_finset_generators (hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F)
    (E : Extension F) (x : Virtual.{uF, uV} F E) :
    ∃ S₀ : Finset (Virtual.{uF, uV} F E),
      (S₀ : Set (Virtual.{uF, uV} F E)) ⊆ characterDifferenceInductionGenerators.{uF, uV} F E ∧
      x - degree F E x • ExactGrothendieckGroup.characterClass
          (1 : weilSubgroup F E →ₜ* ℂˣ) ∈ Submodule.span ℤ (S₀ : Set (Virtual.{uF, uV} F E)) := by
  have hmem : x - degree F E x • ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
        Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) := by
    rw [hgen E]
    change degree F E _ = 0
    simp
  obtain ⟨S₀, hS₀, hx⟩ := Submodule.mem_span_finite_of_mem_span hmem
  exact ⟨S₀, hS₀, hx⟩

/-- The formula for one class from the formula on finitely many generators that
span its degree-zero part, and on the trivial character. -/
theorem mem_formulaSubgroup_of_span {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : IsSystem F e ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (s : ℂ) (a : Virtual.{uF, uV} F E →+ ℂ)
    (S₀ : Set (Virtual.{uF, uV} F E)) (hS₀ : S₀ ⊆ formulaSubgroup hε E ψ μ s a)
    (hone : ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      formulaSubgroup hε E ψ μ s a)
    (x : Virtual.{uF, uV} F E)
    (hx : x - degree F E x • ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F E →ₜ* ℂˣ) ∈ Submodule.span ℤ S₀) :
    (ε E ψ μ (virtualTwist F E s x) : ℂ) =
      ε E ψ μ x * Complex.exp (-s * (a x +
        ((fieldData F E).additiveConductor ψ : ℂ) * (degree F E x : ℂ) *
          logCardinality E)) := by
  let S := formulaSubgroup hε E ψ μ s a
  have hy : x - degree F E x • ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F E →ₜ* ℂˣ) ∈ S :=
    (Submodule.span_le.mpr (show S₀ ⊆ (AddSubgroup.toIntSubmodule S : Set _) from hS₀)) hx
  have := S.add_mem hy (S.zsmul_mem hone (degree F E x))
  rwa [sub_add_cancel] at this

end Langlands.LocalFactor.SpectralConductor
