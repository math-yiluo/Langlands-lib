import Langlands.LocalFactor.DeligneHenniartRelativeWitness
import Langlands.LocalFactor.CommonClosureInductionTensor

/-!
# Induction of relative Deligne--Henniart witnesses

If `γ_L` is a relative witness for `x_L` over a larger field `L`, then its norm is a
relative witness for the induced class over `E`. This is the induction step of DH81 4.5
and 4.8, by the projection formula, induction in degree zero and the norm square of
reciprocity.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The norm square of normalized reciprocity at Weil level: the image of an element of
`W_L` in `W_E` corresponds to the norm of its image in `L^×`. -/
theorem reciprocityUnits_weilInclusion {e : ReciprocityFamily F} (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field) (g : weilSubgroup F L) :
    reciprocityUnits F e E (weilInclusion F E L h g) =
      E.unitsNorm L h (reciprocityUnits F e L g) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let := (fieldData F E).topology
  let := (fieldData F L).topology
  exact DFunLike.congr_fun (he.1.1 E L h) (LocalClassField.abelianizationProjection (weilSubgroup F L) g)

/-- The field determinant of a restricted class at `γ` is that of the class at the norm. -/
theorem fieldDeterminant_continuousRestrict {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e) (E L : Extension F) (h : E.field ≤ L.field)
    (w : Virtual.{uF, uV} F E) (γ : L.fieldˣ) :
    fieldDeterminant F e L (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h) w) γ =
      fieldDeterminant F e E w (E.unitsNorm L h γ) := by
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F e L γ
  rw [fieldDeterminant_reciprocityUnits, ← reciprocityUnits_weilInclusion F he,
    fieldDeterminant_reciprocityUnits]
  unfold ExactGrothendieckGroup.continuousRestrict
  rw [ExactGrothendieckGroup.determinantCharacter_restrict]
  rfl

/-! ## Test spans -/

/-- The subgroup `N ∩ W_L` of `W_L`, for a subgroup `N` of `W_E` and `E ⊆ L`. -/
abbrev restrictSubgroup (E L : Extension F) (h : E.field ≤ L.field)
    (N : Subgroup (weilSubgroup F E)) : Subgroup (weilSubgroup F L) :=
  N.comap (weilInclusion F E L h).toMonoidHom

/-- Restriction to `W_L` sends tests trivial on `N` to tests trivial on `N ∩ W_L`. -/
theorem continuousRestrict_mem_weilTrivialOnSpan (E L : Extension F) (h : E.field ≤ L.field)
    (N : Subgroup (weilSubgroup F E)) {w : Virtual.{uF, uV} F E}
    (hw : w ∈ weilTrivialOnSpan.{uF, uV} F E N) :
    ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h) w ∈
      weilTrivialOnSpan.{uF, uV} F L (restrictSubgroup F E L h N) := by
  have hle : weilTrivialOnSpan.{uF, uV} F E N ≤
      (weilTrivialOnSpan.{uF, uV} F L (restrictSubgroup F E L h N)).comap
        (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h)) := by
    unfold weilTrivialOnSpan
    rw [Submodule.span_le]
    rintro _ ⟨A, hc, hA, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨FiniteRepresentation.restrict (weilInclusion F E L h).toMonoidHom A,
      FiniteRepresentation.isContinuous_restrict _ (weilInclusion F E L h).continuous hc,
      fun n hn => hA _ hn, ?_⟩
    unfold ExactGrothendieckGroup.continuousRestrict
    rw [ExactGrothendieckGroup.restrict_ofRepresentation]
  exact hle hw

/-- Tests trivial on a larger subgroup are tests trivial on a smaller one. -/
theorem weilTrivialOnSpan_antitone (E : Extension F) {N N' : Subgroup (weilSubgroup F E)}
    (hNN' : N ≤ N') : weilTrivialOnSpan.{uF, uV} F E N' ≤ weilTrivialOnSpan.{uF, uV} F E N := by
  apply Submodule.span_mono
  rintro _ ⟨A, hc, hA, rfl⟩
  exact ⟨A, hc, fun n hn => hA n (hNN' hn), rfl⟩

theorem continuousRestrict_mem_degreeZero (E L : Extension F) (h : E.field ≤ L.field)
    {w : Virtual.{uF, uV} F E} (hw : w ∈ DegreeZero.{uF, uV} F E) :
    ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h) w ∈
      DegreeZero.{uF, uV} F L := by
  rw [ExactGrothendieckGroup.mem_degreeZero] at hw ⊢
  rw [ExactGrothendieckGroup.degree_continuousRestrict]
  exact hw

theorem continuousTensorSame_mem_degreeZero (E : Extension F) {w : Virtual.{uF, uV} F E}
    (hw : w ∈ DegreeZero.{uF, uV} F E) (x : Virtual.{uF, uV} F E) :
    ExactGrothendieckGroup.continuousTensorSame w x ∈ DegreeZero.{uF, uV} F E := by
  rw [ExactGrothendieckGroup.mem_degreeZero] at hw ⊢
  rw [ExactGrothendieckGroup.degree_continuousTensor, hw, zero_mul]

variable {F}

/-! ## Monotonicity and additivity of relative witnesses -/

theorem exactWitnessOn_mono {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    {E : Extension F} {N N' : Subgroup (weilSubgroup F E)} (hNN' : N ≤ N')
    {ψ : AdditiveCharacter F E} {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (hx : ExactWitnessOn F e ε E N ψ x γ) : ExactWitnessOn F e ε E N' ψ x γ :=
  fun w hw hw0 μ => hx w (weilTrivialOnSpan_antitone F E hNN' hw) hw0 μ

theorem approximateWitnessOn_mono {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    {E : Extension F} {N N' : Subgroup (weilSubgroup F E)} (hNN' : N ≤ N')
    {ψ : AdditiveCharacter F E} {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (hx : ApproximateWitnessOn F e ε E N ψ x γ) : ApproximateWitnessOn F e ε E N' ψ x γ :=
  fun w hw hw0 μ => hx w (weilTrivialOnSpan_antitone F E hNN' hw) hw0 μ

theorem exactWitnessOn_zero {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} : ExactWitnessOn F e ε E N ψ 0 1 := by
  intro w _ _ μ
  rw [map_zero, value_zero hε, map_one]

theorem exactWitnessOn_add {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} {x y : Virtual.{uF, uV} F E} {γ γ' : E.fieldˣ}
    (hx : ExactWitnessOn F e ε E N ψ x γ) (hy : ExactWitnessOn F e ε E N ψ y γ') :
    ExactWitnessOn F e ε E N ψ (x + y) (γ * γ') := by
  intro w hw hw0 μ
  rw [map_add, hε, hx w hw hw0 μ, hy w hw hw0 μ, map_mul]

theorem exactWitnessOn_zsmul {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} (n : ℤ) {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (hx : ExactWitnessOn F e ε E N ψ x γ) :
    ExactWitnessOn F e ε E N ψ (n • x) (γ ^ n) := by
  intro w hw hw0 μ
  rw [map_zsmul, value_zsmul F hε, hx w hw hw0 μ, map_zpow]

theorem approximateWitnessOn_zero {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} : ApproximateWitnessOn F e ε E N ψ 0 1 := by
  intro w _ _ μ
  exact ⟨0, by rw [map_zero, value_zero hε, map_one]⟩

theorem approximateWitnessOn_add {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} {x y : Virtual.{uF, uV} F E} {γ γ' : E.fieldˣ}
    (hx : ApproximateWitnessOn F e ε E N ψ x γ) (hy : ApproximateWitnessOn F e ε E N ψ y γ') :
    ApproximateWitnessOn F e ε E N ψ (x + y) (γ * γ') := by
  intro w hw hw0 μ
  obtain ⟨n, hn⟩ := hx w hw hw0 μ
  obtain ⟨m, hm⟩ := hy w hw hw0 μ
  refine ⟨n + m, ?_⟩
  have h1 : ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame w x) ^ (p ^ (n + m)) =
      fieldDeterminant F e E w γ ^ (p ^ (n + m)) := by
    rw [pow_add, pow_mul, pow_mul, hn]
  have h2 : ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame w y) ^ (p ^ (n + m)) =
      fieldDeterminant F e E w γ' ^ (p ^ (n + m)) := by
    rw [pow_add, mul_comm (p ^ n), pow_mul, pow_mul, hm]
  rw [map_add, hε, map_mul, mul_pow, mul_pow, h1, h2]

theorem approximateWitnessOn_zsmul {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} (n : ℤ) {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (hx : ApproximateWitnessOn F e ε E N ψ x γ) :
    ApproximateWitnessOn F e ε E N ψ (n • x) (γ ^ n) := by
  intro w hw hw0 μ
  obtain ⟨k, hk⟩ := hx w hw hw0 μ
  refine ⟨k, ?_⟩
  rw [map_zsmul, value_zsmul F hε, map_zpow, ← zpow_natCast, zpow_comm, zpow_natCast, hk,
    ← zpow_natCast, zpow_comm, zpow_natCast]

/-! ## The induction step -/

/-- DH81 4.5 and 4.8, induction step: a witness for `x` over `L`, relative to `N ∩ W_L` and
for the trace character, has norm a witness for the induced class over `E`, relative to `N`. -/
theorem exactWitnessOn_induce {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (E L : Extension F) (h : E.field ≤ L.field)
    (N : Subgroup (weilSubgroup F E)) (ψ : AdditiveCharacter F E)
    (x : Virtual.{uF, uV} F L) (γ : L.fieldˣ)
    (hx : ExactWitnessOn F e ε L (restrictSubgroup F E L h N)
      (traceCharacter F E L h ψ) x γ) :
    ExactWitnessOn F e ε E N ψ (induce F E L h x) (E.unitsNorm L h γ) := by
  intro w hw hw0 μ
  obtain ⟨μL⟩ := exists_haarMeasure F L
  have hwL0 := continuousRestrict_mem_degreeZero F E L h hw0
  have hz := continuousTensorSame_mem_degreeZero F L hwL0 x
  rw [continuousTensorSame_induce, hsys.2.2.2.1 E L h ψ μ μL ⟨_, hz⟩,
    hx _ (continuousRestrict_mem_weilTrivialOnSpan F E L h N hw) hwL0 μL,
    fieldDeterminant_continuousRestrict F hsys.1]

/-- The same induction step for the relation up to roots of unity of `p`-power order. -/
theorem approximateWitnessOn_induce {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (E L : Extension F) (h : E.field ≤ L.field)
    (N : Subgroup (weilSubgroup F E)) (ψ : AdditiveCharacter F E)
    (x : Virtual.{uF, uV} F L) (γ : L.fieldˣ)
    (hx : ApproximateWitnessOn F e ε L (restrictSubgroup F E L h N)
      (traceCharacter F E L h ψ) x γ) :
    ApproximateWitnessOn F e ε E N ψ (induce F E L h x) (E.unitsNorm L h γ) := by
  intro w hw hw0 μ
  obtain ⟨μL⟩ := exists_haarMeasure F L
  have hwL0 := continuousRestrict_mem_degreeZero F E L h hw0
  have hz := continuousTensorSame_mem_degreeZero F L hwL0 x
  obtain ⟨n, hn⟩ := hx _ (continuousRestrict_mem_weilTrivialOnSpan F E L h N hw) hwL0 μL
  refine ⟨n, ?_⟩
  rw [continuousTensorSame_induce, hsys.2.2.2.1 E L h ψ μ μL ⟨_, hz⟩,
    ← fieldDeterminant_continuousRestrict F hsys.1]
  exact hn

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
