import Langlands.LocalFactor.BrauerKernel.LinearTwist
import Langlands.LocalFactor.BrauerKernel.UnramifiedExponent
import Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceProof

/-! # Brauer relations among small twists of a highly ramified norm pullback -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u v

open scoped WithZero

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] (T : F.TopologicalData) (S : E.TopologicalData)

/-- The order in the extension of a base element is its base order times the order of a
base uniformizer. -/
theorem ord_algebraMap_eq_mul (ϖ : F.Carrier) (hϖ : T.ord ϖ = 1) (x : F.Carrier) :
    S.ord (algebraMap F.Carrier E.Carrier x) =
      S.ord (algebraMap F.Carrier E.Carrier ϖ) * T.ord x := by
  have kx := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap F E T S x
  have kϖ := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap F E T S ϖ
  rw [hϖ, mul_one] at kϖ
  apply mul_left_cancel₀ (show (T.ramificationIndex : ℤ) ≠ 0 by
    exact_mod_cast T.ramificationIndex_pos.ne')
  rw [kx, ← mul_assoc, kϖ]

/-- A base uniformizer has positive order in the extension. -/
theorem ord_algebraMap_pos (ϖ : F.Carrier) (hϖ : T.ord ϖ = 1) :
    0 < S.ord (algebraMap F.Carrier E.Carrier ϖ) := by
  have kϖ := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap F E T S ϖ
  rw [hϖ, mul_one] at kϖ
  have h1 : (0 : ℤ) < T.ramificationIndex := by exact_mod_cast T.ramificationIndex_pos
  have h2 : (0 : ℤ) < S.ramificationIndex := by exact_mod_cast S.ramificationIndex_pos
  by_contra hle
  push Not at hle
  nlinarith

/-- An element of trace one bounds the additive conductor of the trace pullback above. -/
theorem additiveConductor_traceCharacter_lt
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ϖ : F.Carrier) (hϖ : T.ord ϖ = 1) (x₀ : E.Carrier)
    (hx₀ : Algebra.trace F.Carrier E.Carrier x₀ = 1) :
    S.additiveConductor (T.traceCharacter S ψ) <
      S.ord (algebraMap F.Carrier E.Carrier ϖ) * (T.additiveConductor ψ + 1) - S.ord x₀ := by
  let := T.topology
  obtain ⟨w, hw, hψw⟩ := T.exists_nontrivial_at_conductor_succ ψ
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hψw (AddChar.map_zero_eq_one _)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    simp at hx₀
  have hr := T.ord_algebraMap_pos S ϖ hϖ
  have hiw : algebraMap F.Carrier E.Carrier w ≠ 0 := (map_ne_zero _).mpr hw0
  have hx0 : algebraMap F.Carrier E.Carrier w * x₀ ≠ 0 := mul_ne_zero hiw hx₀0
  have hwo : -(T.additiveConductor ψ + 1) ≤ T.ord w := by
    rwa [T.mem_additiveLattice, LocalFactor.PadicAbelian.gauss_valuation_le_exp_iff T hw0] at hw
  have hx : algebraMap F.Carrier E.Carrier w * x₀ ∈ S.additiveLattice
      (S.ord (algebraMap F.Carrier E.Carrier ϖ) * (T.additiveConductor ψ + 1) - S.ord x₀) := by
    rw [S.mem_additiveLattice, LocalFactor.PadicAbelian.gauss_valuation_le_exp_iff S hx0,
      S.ord_mul hiw hx₀0, T.ord_algebraMap_eq_mul S ϖ hϖ w]
    nlinarith
  by_contra hle
  push Not at hle
  have htriv := (S.additiveConductor_spec (T.traceCharacter S ψ)).1 _
    (S.additiveLattice_mono hle hx)
  rw [traceCharacter_apply, ← Algebra.smul_def, map_smul, hx₀, smul_eq_mul, mul_one] at htriv
  exact hψw htriv

/-- **Norm pullbacks keep a deep linearization.** If `α(z) = ψ(c (z - 1))` on `U^n` of the
base, then for a suitable integral `a`, the norm pullback `β = α ∘ N` satisfies
`β(1 + x) = (ψ ∘ Tr)(c x)` on every lattice inside `a O`. -/
theorem normPullback_linearization
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (c : F.Carrier) (n : ℕ) (α : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology)
    (hα : ∀ z : T.principalUnits n,
      α (z : F.Carrierˣ) = Circle.toUnits (ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1))))
    (a : F.Carrier) (haI : a ∈ T.Integers) (ha0 : a ≠ 0)
    (ha : T.discreteValuation a < 1) (hlevel : T.discreteValuation a ≤ WithZero.exp (-(n : ℤ)))
    (hquad : T.discreteValuation c * T.discreteValuation a ^ 2 ≤
      WithZero.exp (T.additiveConductor ψ))
    (β : @HarmonicAnalysis.Quasicharacter E.Carrier _ S.topology)
    (hβ : ∀ x, β x = α (LocalClassField.normUnits F.Carrier E.Carrier x))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hm₀a : S.ord (algebraMap F.Carrier E.Carrier a) ≤ m₀) :
    letI := S.topology
    ∀ x : S.additiveLattice (-(m₀ : ℤ)),
      (β (LocalFactor.RankOneStability.oneAddUnit S hm₀ x) : ℂ) =
        (T.traceCharacter S ψ).complex (algebraMap F.Carrier E.Carrier c * x.val) := by
  let := S.topology
  intro x
  set A := algebraMap F.Carrier E.Carrier a with hA
  have hA0 : A ≠ 0 := (map_ne_zero _).mpr ha0
  have hxA : A * (A⁻¹ * x.val) = x.val := by rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul]
  have hy : A⁻¹ * x.val ∈ S.Integers := by
    rw [← S.mem_additiveLattice_zero]
    have h := (S.mul_mem_additiveLattice_iff hA0 _ _).mp (hxA.symm ▸ x.2)
    exact S.additiveLattice_mono (by omega) h
  obtain ⟨z, hz, -, hχ⟩ := HarmonicAnalysis.padicDeepUnitNormTrace p F E T S ψ c n α hα
    ⟨a, haI⟩ ha hlevel hquad ⟨A⁻¹ * x.val, hy⟩
  have hzeq : LocalFactor.RankOneStability.oneAddUnit S hm₀ x = z := by
    apply Units.ext
    rw [LocalFactor.RankOneStability.oneAddUnit_val, hz]
    change 1 + x.val = 1 + A * (A⁻¹ * x.val)
    rw [hxA]
  rw [hzeq, hβ]
  change ((α (Units.map (Algebra.norm F.Carrier) z) : ℂˣ) : ℂ) = _
  rw [hχ, Circle.toUnits_apply, Units.val_mk0,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, traceCharacter_apply]
  congr 2
  change c * a * Algebra.trace F.Carrier E.Carrier (A⁻¹ * x.val) = _
  conv_rhs => rw [← hxA, ← mul_assoc, hA, ← map_mul, ← Algebra.smul_def, map_smul,
    smul_eq_mul]

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The epsilon values of a generator are small twists of one epsilon value, by a common
base element. Then the generator value is the character ratio at that element. -/
theorem generatorValue_of_twistFactor {E : Extension F} (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (g : Generator F E) (γ : E.fieldˣ)
    (β χ₀ χ₀' : FieldCharacter F g.extension) (h₁ : g.first = χ₀ * β) (h₂ : g.second = χ₀' * β)
    (hε : (fieldData F g.extension).abelianEpsilonExpression (χ₀ * β)
        (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension) =
      (χ₀ (E.unitsInclusion g.extension g.inclusion γ) : ℂ) *
        (fieldData F g.extension).abelianEpsilonExpression β
          (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension))
    (hε' : (fieldData F g.extension).abelianEpsilonExpression (χ₀' * β)
        (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension) =
      (χ₀' (E.unitsInclusion g.extension g.inclusion γ) : ℂ) *
        (fieldData F g.extension).abelianEpsilonExpression β
          (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension)) :
    generatorValue F E ψ measures g = generatorCharacterRatio F E g γ := by
  let T := fieldData F g.extension
  let := T.topology
  let ψL := traceCharacter F E g.extension g.inclusion ψ
  let i := E.unitsInclusion g.extension g.inclusion γ
  have hunit (ω : FieldCharacter F g.extension)
      (h : T.abelianEpsilonExpression (ω * β) ψL (measures g.extension) =
        (ω i : ℂ) * T.abelianEpsilonExpression β ψL (measures g.extension)) :
      T.abelianEpsilonUnit (ω * β) ψL (measures g.extension) =
        ω i * T.abelianEpsilonUnit β ψL (measures g.extension) := by
    apply Units.ext
    rw [Units.val_mul, PadicField.TopologicalData.coe_abelianEpsilonUnit,
      PadicField.TopologicalData.coe_abelianEpsilonUnit, h]
  change T.abelianEpsilonUnit g.first ψL (measures g.extension) /
      T.abelianEpsilonUnit g.second ψL (measures g.extension) = _
  rw [h₁, h₂, hunit χ₀ hε, hunit χ₀' hε', mul_div_mul_right_eq_div, generatorCharacterRatio,
    h₁, h₂]
  change χ₀ i / χ₀' i = (χ₀ * β) i / (χ₀' * β) i
  rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.mul_apply, mul_div_mul_right_eq_div]

/-- **Brauer relations among common twist factors.** If every generator of an actual relation
has characters `χ₀ β` and `χ₀' β` whose epsilon values are `χ₀(γ) ε(β)` and `χ₀'(γ) ε(β)` for
one base element `γ`, then the abelian epsilon evaluation of the relation is trivial. -/
theorem evaluationMap_eq_zero_of_twistFactor (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) (γ : E.fieldˣ)
    (hgen : ∀ g ∈ z.support, ∃ β χ₀ χ₀' : FieldCharacter F g.extension,
      g.first = χ₀ * β ∧ g.second = χ₀' * β ∧
      (fieldData F g.extension).abelianEpsilonExpression (χ₀ * β)
          (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension) =
        (χ₀ (E.unitsInclusion g.extension g.inclusion γ) : ℂ) *
          (fieldData F g.extension).abelianEpsilonExpression β
            (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension) ∧
      (fieldData F g.extension).abelianEpsilonExpression (χ₀' * β)
          (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension) =
        (χ₀' (E.unitsInclusion g.extension g.inclusion γ) : ℂ) *
          (fieldData F g.extension).abelianEpsilonExpression β
            (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension)) :
    evaluationMap F E ψ measures z = 0 := by
  have hrat := characterRatioMap_eq_zero.{uF, uV} F e he E z hz γ
  have heval : evaluationMap F E ψ measures z = characterRatioMap F E γ z := by
    rw [evaluationMap, characterRatioMap, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨β, χ₀, χ₀', h₁, h₂, hε, hε'⟩ := hgen g hg
    rw [generatorValue_of_twistFactor F ψ measures g γ β χ₀ χ₀' h₁ h₂ hε hε']
  rw [heval, hrat]

/-- The unit `c` linearizes `α` for `ψ` at the half level: `c` has the exact order
`-(a(α) + n(ψ))`, and `α(z) = ψ(c (z - 1))` for every `z ∈ U^(a(α) - ⌊a(α)/2⌋)`. -/
def IsHalfLinearizer (E : Extension F) (ψ : AdditiveCharacter F E) (α : FieldCharacter F E)
    (c : E.fieldˣ) : Prop :=
  letI := (fieldData F E).topology
  (fieldData F E).ord (c : E.field) =
      -(((fieldData F E).multiplicativeConductor α : ℤ) + (fieldData F E).additiveConductor ψ) ∧
    ∀ z ∈ (fieldData F E).principalUnits ((fieldData F E).multiplicativeConductor α -
        (fieldData F E).multiplicativeConductor α / 2),
      (α z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1))

/-- Every character of conductor at least two has a half-level linearizer. -/
theorem exists_isHalfLinearizer (E : Extension F) (ψ : AdditiveCharacter F E)
    (α : FieldCharacter F E) (hα : 2 ≤ (fieldData F E).multiplicativeConductor α) :
    ∃ c : E.fieldˣ, IsHalfLinearizer F E ψ α c := by
  let T := fieldData F E
  let := T.topology
  set A := T.multiplicativeConductor α with hAdef
  have hm : 0 < A - A / 2 := by omega
  obtain ⟨c, hc0, hc, hlin⟩ := LocalFactor.RankOneStability.exists_deep_linearization T α ψ hm
    (by omega) (by omega)
  refine ⟨Units.mk0 c hc0, hc, ?_⟩
  intro u hu
  have hx : (u : E.field) - 1 ∈ T.additiveLattice (-((A - A / 2 : ℕ) : ℤ)) := hu.2
  have heq : LocalFactor.RankOneStability.oneAddUnit T hm ⟨_, hx⟩ = u := by
    apply Units.ext
    simp
  have h := hlin ⟨_, hx⟩
  rw [heq] at h
  exact h

/-- **Highly ramified norm pullbacks absorb small twists.** For a nested field `L ⊇ E` and a
bound `K` there is `B` with the following property. Let `α` have conductor `a(α) ≥ B`, and let
`c` be a half-level linearizer of `α` (`IsHalfLinearizer`). Then for every character `χ₀` of `L` with conductor at most `K`, the epsilon value of
`χ₀ · (α ∘ N_{L/E})` for `ψ ∘ Tr_{L/E}` is `χ₀(c)⁻¹` times that of `α ∘ N_{L/E}`. -/
theorem exists_bound_abelianEpsilonExpression_twist (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (K : ℕ) :
    ∃ B : ℕ, ∀ α : FieldCharacter F E, B ≤ (fieldData F E).multiplicativeConductor α →
      ∀ c : E.fieldˣ, IsHalfLinearizer F E ψ α c →
        ∀ χ₀ : FieldCharacter F L, (fieldData F L).multiplicativeConductor χ₀ ≤ K →
        ∀ μ : HaarMeasure F L,
          (fieldData F L).abelianEpsilonExpression (χ₀ * normPullback F e E L h α)
              (traceCharacter F E L h ψ) μ =
            (χ₀ (E.unitsInclusion L h c) : ℂ)⁻¹ *
              (fieldData F L).abelianEpsilonExpression (normPullback F e E L h α)
                (traceCharacter F E L h ψ) μ := by
  let T := fieldData F E
  let S := fieldData F L
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  have : IsScalarTower (Padic p) E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.field L.field := FiniteDimensional.right F.Carrier E.field L.field
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : CharZero E.field := charZero_of_injective_algebraMap (algebraMap F.Carrier E.field).injective
  obtain ⟨x₀, hx₀⟩ := Algebra.trace_surjective E.field L.field 1
  let ϖ : E.field := T.uniformizer
  have hϖ : T.ord ϖ = 1 := T.ord_uniformizer
  let r := S.ord (algebraMap E.field L.field ϖ)
  let t₀ := S.ord x₀
  refine ⟨2 * (K + (-t₀).toNat + 2), ?_⟩
  intro α hB c hcα χ₀ hχ₀ μ
  obtain ⟨hc, hlin⟩ := hcα
  let := T.topology
  let := S.topology
  set A := T.multiplicativeConductor α with hAdef
  set n := T.additiveConductor ψ with hndef
  have ht₀ : -t₀ ≤ ((-t₀).toNat : ℤ) := Int.self_le_toNat (-t₀)
  set mE := A - A / 2 with hmEdef
  have hmE : 0 < mE := by omega
  let a : E.field := ϖ ^ mE
  have hϖ0 : ϖ ≠ 0 := T.coordinateUniformizer_ne_zero ϖ hϖ
  have ha0 : a ≠ 0 := pow_ne_zero _ hϖ0
  have hoa : T.ord a = mE := by
    rw [show a = ϖ ^ (mE : ℤ) from (zpow_natCast _ _).symm, T.ord_zpow, hϖ, mul_one]
  have hva : T.discreteValuation a = WithZero.exp (-(mE : ℤ)) := by
    rw [LocalFactor.PadicAbelian.gauss_valuation_eq_exp_neg_ord T ha0, hoa]
  have haI : a ∈ T.Integers := by
    rw [← T.mem_additiveLattice_zero, T.mem_additiveLattice, hva, WithZero.exp_le_exp]
    omega
  have ha : T.discreteValuation a < 1 := by
    rw [hva, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hquad : T.discreteValuation (c : E.field) * T.discreteValuation a ^ 2 ≤
      WithZero.exp (T.additiveConductor ψ) := by
    rw [LocalFactor.PadicAbelian.gauss_valuation_eq_exp_neg_ord T c.ne_zero, hc, hva,
      ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp, nsmul_eq_mul]
    push_cast
    omega
  have hα : ∀ z : T.principalUnits mE,
      α (z : E.fieldˣ) = Circle.toUnits (ψ ((c : E.field) * (((z : E.fieldˣ) : E.field) - 1))) := by
    intro z
    apply Units.ext
    rw [Circle.toUnits_apply, Units.val_mk0, hlin z z.2,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]
  let β := normPullback F e E L h α
  have hβ : ∀ x, β x = α (LocalClassField.normUnits E.field L.field x) :=
    fun x => normPullback_apply F e he E L h α x
  have hr : 0 < r := T.ord_algebraMap_pos S ϖ hϖ
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : ℕ, (m₀ : ℤ) = r * mE :=
    ⟨(r * mE).toNat, Int.toNat_of_nonneg (by positivity)⟩
  have hrm : 1 ≤ r * mE := by nlinarith
  have hm₀ : 0 < m₀ := by omega
  have hm₀a : S.ord (algebraMap E.field L.field a) ≤ m₀ := by
    rw [T.ord_algebraMap_eq_mul S ϖ hϖ, hoa, hm₀def]
  have hlinL := T.normPullback_linearization S ψ (c : E.field) mE α hα a haI ha0 ha
    hva.le hquad β hβ hm₀ hm₀a
  let cL := E.unitsInclusion L h c
  have hordL : S.ord (cL : L.field) = -(r * (A + n)) := by
    change S.ord (algebraMap E.field L.field (c : E.field)) = _
    rw [T.ord_algebraMap_eq_mul S ϖ hϖ, hc]
    ring
  have hnL : S.additiveConductor (T.traceCharacter S ψ) < r * (n + 1) - t₀ :=
    T.additiveConductor_traceCharacter_lt S ψ ϖ hϖ x₀ hx₀
  have hAm : ((A : ℤ) - mE - 1) ≥ K + (-t₀).toNat + 1 := by omega
  have hA1 : (A : ℤ) - 1 ≥ 2 * K + 2 * (-t₀).toNat + 3 := by omega
  have hbig₁ : S.ord (cL : L.field) + ((m₀ + (K + 1) : ℕ) : ℤ) ≤
      -S.additiveConductor (T.traceCharacter S ψ) := by
    rw [hordL]
    push_cast
    rw [hm₀def]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ r - 1 by omega)
      (show (0 : ℤ) ≤ (A : ℤ) - mE - 1 by omega)]
  have hbig₂ : S.ord (cL : L.field) + ((2 * (K + 1) : ℕ) : ℤ) ≤
      -S.additiveConductor (T.traceCharacter S ψ) := by
    rw [hordL]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ r - 1 by omega)
      (show (0 : ℤ) ≤ (A : ℤ) - 1 by omega)]
  have key := LocalFactor.RankOneStability.abelianEpsilonExpression_mul_of_linearization S β
    (T.traceCharacter S ψ) cL hm₀ hlinL (K + 1) (by omega) hbig₁ hbig₂ χ₀
    (hχ₀.trans (Nat.le_succ K)) μ
  rw [mul_comm β χ₀, map_inv, Units.val_inv_eq_inv_val] at key
  exact key

/-- **Brauer relations among small twists of a highly ramified norm pullback.** For finitely
many nested fields and a conductor bound `K` there is `B` with the following property. If
`a(α) ≥ B` and every generator of an actual relation lies over one of these fields, with
characters `χ₀ · (α ∘ N)` and `χ₀' · (α ∘ N)` of conductors `a(χ₀), a(χ₀') ≤ K`, then the
abelian epsilon evaluation of the relation is trivial. -/
theorem exists_bound_evaluationMap_eq_zero_of_ramified_normPullback (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (Ls : Finset (Extension F)) (K : ℕ) :
    ∃ B : ℕ, ∀ α : FieldCharacter F E, B ≤ (fieldData F E).multiplicativeConductor α →
      ∀ z : Presentation F E, presentationMap.{uF, uV} F e E z = 0 →
      (∀ g ∈ z.support, g.extension ∈ Ls ∧ ∃ χ₀ χ₀' : FieldCharacter F g.extension,
        (fieldData F g.extension).multiplicativeConductor χ₀ ≤ K ∧
        (fieldData F g.extension).multiplicativeConductor χ₀' ≤ K ∧
        g.first = χ₀ * normPullback F e E g.extension g.inclusion α ∧
        g.second = χ₀' * normPullback F e E g.extension g.inclusion α) →
      evaluationMap F E ψ measures z = 0 := by
  classical
  let bound : Extension F → ℕ := fun L => if h : E.field ≤ L.field then
    (exists_bound_abelianEpsilonExpression_twist F e he E L h ψ K).choose else 0
  refine ⟨max 2 (Ls.sup bound), ?_⟩
  intro α hα z hz hgen
  let T := fieldData F E
  let := T.topology
  obtain ⟨d, hd⟩ := exists_isHalfLinearizer F E ψ α (le_trans (le_max_left _ _) hα)
  apply evaluationMap_eq_zero_of_twistFactor F e he E ψ measures z hz d⁻¹
  intro g hg
  obtain ⟨hL, χ₀, χ₀', hχ₀, hχ₀', h₁, h₂⟩ := hgen g hg
  have hspec :=
    (exists_bound_abelianEpsilonExpression_twist F e he E g.extension g.inclusion ψ K).choose_spec
  have hB : (exists_bound_abelianEpsilonExpression_twist F e he E g.extension g.inclusion ψ
      K).choose ≤ T.multiplicativeConductor α := by
    have h1 : bound g.extension ≤ Ls.sup bound := Finset.le_sup hL
    have h2 : bound g.extension = (exists_bound_abelianEpsilonExpression_twist F e he E
        g.extension g.inclusion ψ K).choose := by
      simp only [bound, g.inclusion, dite_true]
    rw [h2] at h1
    exact h1.trans ((le_max_right _ _).trans hα)
  have key := hspec α hB d hd
  have hinv : E.unitsInclusion g.extension g.inclusion d⁻¹ =
      (E.unitsInclusion g.extension g.inclusion d)⁻¹ := map_inv _ _
  refine ⟨normPullback F e E g.extension g.inclusion α, χ₀, χ₀', h₁, h₂, ?_, ?_⟩
  · rw [key χ₀ hχ₀, hinv, map_inv χ₀, Units.val_inv_eq_inv_val]
  · rw [key χ₀' hχ₀', hinv, map_inv χ₀', Units.val_inv_eq_inv_val]

end Langlands.LocalFactor.NonabelianBrauer
