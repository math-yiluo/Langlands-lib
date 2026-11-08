import Langlands.LocalFactor.DeligneHenniartWitnessGroups
import Langlands.LocalFactor.CommonClosureRelativeDegreeZeroBrauer
import Langlands.LocalFactor.CommonClosureInductionTwist
import Langlands.LocalFactor.NonabelianDeterminantTransfer
import Langlands.LocalFactor.CommonClosureRankOneEpsilon
import Langlands.LocalFactor.NonabelianRankOneScaling
import Langlands.LocalFactor.Inductive.GallagherDeterminantProof
import Langlands.LocalFactor.DeligneHenniartUpperUnits
import Langlands.LocalFactor.Ramification.WeilBreakStatement
import Langlands.Weil.Local.AssemblyProof

/-! # Deligne--Henniart witnesses relative to a normal subgroup -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-! ## Additivity of the two sides -/

theorem fieldDeterminant_add_apply (e : ReciprocityFamily F) (E : Extension F)
    (x y : Virtual.{uF, uV} F E) (γ : E.fieldˣ) :
    fieldDeterminant F e E (x + y) γ =
      fieldDeterminant F e E x γ * fieldDeterminant F e E y γ := by
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F e E γ
  simp only [fieldDeterminant_reciprocityUnits,
    ExactGrothendieckGroup.determinantCharacter_add_apply]

theorem fieldDeterminant_zero_apply (e : ReciprocityFamily F) (E : Extension F)
    (γ : E.fieldˣ) : fieldDeterminant.{uF, uV} F e E 0 γ = 1 := by
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F e E γ
  simp only [fieldDeterminant_reciprocityUnits,
    ExactGrothendieckGroup.determinantCharacter_zero_apply]

theorem fieldDeterminant_zsmul_apply (e : ReciprocityFamily F) (E : Extension F)
    (n : ℤ) (x : Virtual.{uF, uV} F E) (γ : E.fieldˣ) :
    fieldDeterminant F e E (n • x) γ = fieldDeterminant F e E x γ ^ n := by
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F e E γ
  simp only [fieldDeterminant_reciprocityUnits,
    ExactGrothendieckGroup.determinantCharacter_zsmul_apply]

theorem value_zsmul {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (n : ℤ)
    (x : Virtual.{uF, uV} F E) : ε E ψ μ (n • x) = ε E ψ μ x ^ n := by
  have h := map_zsmul (valueAddHom F ε hε E ψ μ) n x
  change Additive.ofMul (ε E ψ μ (n • x)) = n • Additive.ofMul (ε E ψ μ x) at h
  rw [← ofMul_zpow] at h
  exact Additive.ofMul.injective h

theorem value_sub {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x y : Virtual.{uF, uV} F E) : ε E ψ μ (x - y) = ε E ψ μ x * (ε E ψ μ y)⁻¹ := by
  rw [sub_eq_add_neg, hε, value_neg hε]

/-- Every finite intermediate field carries an additive Haar measure. -/
theorem exists_haarMeasure (E : Extension F) : Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

/-! ## Witnesses relative to a subgroup -/

/-- The exact twisting relation over `E`, tested on all degree-zero classes
spanned by continuous representations of `W_E` on which `N` acts trivially. -/
def ExactWitnessOn (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F) (E : Extension F)
    (N : Subgroup (weilSubgroup F E)) (ψ : AdditiveCharacter F E)
    (x : Virtual.{uF, uV} F E) (γ : E.fieldˣ) : Prop :=
  ∀ w ∈ weilTrivialOnSpan.{uF, uV} F E N, w ∈ DegreeZero.{uF, uV} F E →
    ∀ μ : HaarMeasure F E,
      ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame w x) = fieldDeterminant F e E w γ

/-- The relation up to roots of unity of `p`-power order, on the same tests. -/
def ApproximateWitnessOn (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (E : Extension F) (N : Subgroup (weilSubgroup F E)) (ψ : AdditiveCharacter F E)
    (x : Virtual.{uF, uV} F E) (γ : E.fieldˣ) : Prop :=
  ∀ w ∈ weilTrivialOnSpan.{uF, uV} F E N, w ∈ DegreeZero.{uF, uV} F E →
    ∀ μ : HaarMeasure F E, ∃ n : ℕ,
      ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame w x) ^ (p ^ n) =
        fieldDeterminant F e E w γ ^ (p ^ n)

variable {F}

/-- The exact relation on a spanning set of the tests gives it on all tests. -/
theorem exactWitnessOn_of_span {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (S : Set (Virtual.{uF, uV} F E))
    (hS : ∀ w ∈ weilTrivialOnSpan.{uF, uV} F E N, w ∈ DegreeZero.{uF, uV} F E →
      w ∈ Submodule.span ℤ S)
    (h : ∀ y ∈ S, ∀ μ : HaarMeasure F E,
      ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame y x) = fieldDeterminant F e E y γ) :
    ExactWitnessOn F e ε E N ψ x γ := by
  intro w hw hw0 μ
  have hmem := hS w hw hw0
  clear hw hw0
  induction hmem using Submodule.span_induction with
  | mem y hy => exact h y hy μ
  | zero =>
    rw [map_zero, LinearMap.zero_apply, value_zero hε, fieldDeterminant_zero_apply]
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply, hε, hy, hz, fieldDeterminant_add_apply]
  | smul n y _ hy =>
    rw [map_zsmul, LinearMap.smul_apply, value_zsmul F hε, hy, fieldDeterminant_zsmul_apply]

/-- The ratio of the two sides, in additive notation on complex units. -/
private def ratioHom (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : AdditiveRelation F ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (x : Virtual.{uF, uV} F E) (γ : E.fieldˣ) :
    Virtual.{uF, uV} F E →+ Additive ℂˣ where
  toFun y := Additive.ofMul (ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame y x)) -
    Additive.ofMul (fieldDeterminant F e E y γ)
  map_zero' := by
    rw [map_zero, LinearMap.zero_apply, value_zero hε, fieldDeterminant_zero_apply, sub_self]
  map_add' y z := by
    rw [map_add, LinearMap.add_apply, hε, fieldDeterminant_add_apply, ofMul_mul, ofMul_mul]
    abel

private theorem ratioHom_mem_iff (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : AdditiveRelation F ε) (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (x y : Virtual.{uF, uV} F E) (γ : E.fieldˣ) :
    ratioHom e ε hε E ψ μ x γ y ∈ pPowerTorsion p (Additive ℂˣ) ↔
      ∃ n : ℕ, ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame y x) ^ (p ^ n) =
        fieldDeterminant F e E y γ ^ (p ^ n) := by
  change (∃ n : ℕ, (p ^ n) • (Additive.ofMul _ - Additive.ofMul _) = (0 : Additive ℂˣ)) ↔ _
  simp only [nsmul_sub, sub_eq_zero]
  rfl

/-- The approximate relation on a spanning set of the tests gives it on all tests. -/
theorem approximateWitnessOn_of_span {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hε : AdditiveRelation F ε) {E : Extension F} {N : Subgroup (weilSubgroup F E)}
    {ψ : AdditiveCharacter F E} {x : Virtual.{uF, uV} F E} {γ : E.fieldˣ}
    (S : Set (Virtual.{uF, uV} F E))
    (hS : ∀ w ∈ weilTrivialOnSpan.{uF, uV} F E N, w ∈ DegreeZero.{uF, uV} F E →
      w ∈ Submodule.span ℤ S)
    (h : ∀ y ∈ S, ∀ μ : HaarMeasure F E, ∃ n : ℕ,
      ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame y x) ^ (p ^ n) =
        fieldDeterminant F e E y γ ^ (p ^ n)) :
    ApproximateWitnessOn F e ε E N ψ x γ := by
  intro w hw hw0 μ
  rw [← ratioHom_mem_iff e ε hε]
  have hmem := hS w hw hw0
  clear hw hw0
  induction hmem using Submodule.span_induction with
  | mem y hy => exact (ratioHom_mem_iff e ε hε E ψ μ x y γ).mpr (h y hy μ)
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact AddSubgroup.add_mem _ hy hz
  | smul n y _ hy => rw [map_zsmul]; exact AddSubgroup.zsmul_mem _ hy n

/-! ## Induced rank-one tests against a character class -/

variable (F)

/-- A field character of `E`, restricted to the Weil subgroup of `L ⊇ E` and read
as a field character of `L` through the reciprocity components. -/
def restrictCharacter (e : ReciprocityFamily F) (E L : Extension F) (h : E.field ≤ L.field)
    (χ : FieldCharacter F E) : FieldCharacter F L :=
  CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L
    ((weilCharacter F e E χ).comp (weilInclusion F E L h))

theorem weilCharacter_restrictCharacter (e : ReciprocityFamily F) (E L : Extension F)
    (h : E.field ≤ L.field) (χ : FieldCharacter F E) :
    weilCharacter F e L (restrictCharacter F e E L h χ) =
      (weilCharacter F e E χ).comp (weilInclusion F E L h) :=
  CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv F e L _

/-- Twisting the induced test `Ind (η - 1)` by a character class `[χ]` gives the
induced degree-zero class `Ind ([χ|·η] - [χ|])`. -/
theorem continuousTensorSame_induce_characterClass (E L : Extension F)
    (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ) (χ : weilSubgroup F E →ₜ* ℂˣ) :
    ExactGrothendieckGroup.continuousTensorSame
        (induce F E L h (ExactGrothendieckGroup.characterClass.{uF, max uF uV} η -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)))
        (ExactGrothendieckGroup.characterClass.{uF, max uF uV} χ) =
      induce F E L h
        (ExactGrothendieckGroup.characterClass.{uF, max uF uV}
            (χ.comp (weilInclusion F E L h) * η) -
          ExactGrothendieckGroup.characterClass (χ.comp (weilInclusion F E L h))) := by
  rw [ExactGrothendieckGroup.continuousTensor_characterClass, continuousTwist_induce, map_sub,
    ExactGrothendieckGroup.continuousTwist_characterClass,
    ExactGrothendieckGroup.continuousTwist_characterClass]
  congr 3
  ext g
  simp

theorem weilCharacter_mul (e : ReciprocityFamily F) (E : Extension F)
    (χ η : FieldCharacter F E) :
    weilCharacter F e E (χ * η) = weilCharacter F e E χ * weilCharacter F e E η :=
  ContinuousMonoidHom.ext fun _ => rfl

theorem weilCharacter_apply (e : ReciprocityFamily F) (E : Extension F)
    (χ : FieldCharacter F E) (g : weilSubgroup F E) :
    weilCharacter F e E χ g = χ (reciprocityUnits F e E g) :=
  rfl

/-- The epsilon side of an induced rank-one test against a character class:
induction in degree zero, then the rank-one law on the larger field. -/
theorem value_induce_characterClass {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (μL : HaarMeasure F L)
    (χ : FieldCharacter F E) (η : weilSubgroup F L →ₜ* ℂˣ) :
    ε E ψ μ (ExactGrothendieckGroup.continuousTensorSame
        (induce F E L h (ExactGrothendieckGroup.characterClass.{uF, max uF uV} η -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)))
        (characterClass F e E χ)) =
      ε L (traceCharacter F E L h ψ) μL (characterClass F e L
          (restrictCharacter F e E L h χ *
            CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)) *
        (ε L (traceCharacter F E L h ψ) μL
          (characterClass F e L (restrictCharacter F e E L h χ)))⁻¹ := by
  have hcc : characterClass F e E χ =
      ExactGrothendieckGroup.characterClass.{uF, max uF uV} (weilCharacter F e E χ) := rfl
  rw [hcc, continuousTensorSame_induce_characterClass]
  set χL := (weilCharacter F e E χ).comp (weilInclusion F E L h) with hχL
  have hz : ExactGrothendieckGroup.characterClass.{uF, max uF uV} (χL * η) -
      ExactGrothendieckGroup.characterClass χL ∈ DegreeZero.{uF, uV} F L := by
    rw [ExactGrothendieckGroup.mem_degreeZero, map_sub,
      ExactGrothendieckGroup.degree_characterClass,
      ExactGrothendieckGroup.degree_characterClass, sub_self]
  rw [hsys.2.2.2.1 E L h ψ μ μL ⟨_, hz⟩, value_sub F hsys.2.1]
  have h1 : χL * η = weilCharacter F e L (restrictCharacter F e E L h χ *
      CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) := by
    rw [weilCharacter_mul, weilCharacter_restrictCharacter,
      CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
  have h2 : χL = weilCharacter F e L (restrictCharacter F e E L h χ) :=
    (weilCharacter_restrictCharacter F e E L h χ).symm
  rw [h1]
  conv_lhs => rw [h2]
  rfl

/-- The determinant side of an induced rank-one test, by Gallagher's theorem and
the transfer/inclusion square of normalized reciprocity. -/
theorem fieldDeterminant_induce_characterClass {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e) (E L : Extension F) (h : E.field ≤ L.field)
    (η : weilSubgroup F L →ₜ* ℂˣ) (γ : E.fieldˣ) :
    fieldDeterminant F e E
        (induce F E L h (ExactGrothendieckGroup.characterClass.{uF, max uF uV} η -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ))) γ =
      CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η (E.unitsInclusion L h γ) := by
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F e E γ
  obtain ⟨v, hv⟩ := reciprocityUnits_surjective F e L
    (E.unitsInclusion L h (reciprocityUnits F e E g))
  have hz : ExactGrothendieckGroup.characterClass.{uF, max uF uV} η -
      ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ) ∈
        DegreeZero.{uF, uV} F L := by
    rw [ExactGrothendieckGroup.mem_degreeZero, map_sub,
      ExactGrothendieckGroup.degree_characterClass,
      ExactGrothendieckGroup.degree_characterClass, sub_self]
  rw [fieldDeterminant_reciprocityUnits,
    determinant_induce_degreeZero_reciprocity F
      (Inductive.gallagherDeterminant.{0, uF, max uF uV}) e he E L h ⟨_, hz⟩ g v hv]
  rw [← hv]
  change ExactGrothendieckGroup.determinantCharacter _ (_ - _) v =
    weilCharacter F e L (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) v
  rw [CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv,
    ExactGrothendieckGroup.determinantCharacter_sub_apply,
    ExactGrothendieckGroup.determinantCharacter_characterClass,
    ExactGrothendieckGroup.determinantCharacter_characterClass]
  simp

/-- DH81 4.4/4.7, representation-theoretic half: a field element is an exact
witness for a character class relative to `N` as soon as the rank-one twist
relation holds on every larger field `L` whose Weil subgroup contains `N`,
for every character of `W_L` trivial on `N`. -/
theorem exactWitnessOn_characterClass {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (hNI : N ≤ CommonClosureWeilDeligne.inertia F E)
    (ψ : AdditiveCharacter F E) (χ : FieldCharacter F E) (γ : E.fieldˣ)
    (hrank : ∀ (L : Extension F) (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ)
      (hNL : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L),
      (∀ n : N, η ⟨((n : weilSubgroup F E) : localWeilGroup F), hNL n n.2⟩ = 1) →
      ∀ μL : HaarMeasure F L,
        (fieldData F L).abelianEpsilonExpression
            (restrictCharacter F e E L h χ *
              CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)
            (traceCharacter F E L h ψ) μL =
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η
              (E.unitsInclusion L h γ) : ℂ) *
            (fieldData F L).abelianEpsilonExpression (restrictCharacter F e E L h χ)
              (traceCharacter F E L h ψ) μL) :
    ExactWitnessOn F e ε E N ψ (characterClass F e E χ) γ := by
  apply exactWitnessOn_of_span hsys.2.1 (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)
    (fun w hw hw0 => weilRelativeDegreeZeroBrauer F E N hN hNI w hw hw0)
  rintro y ⟨L, h, η, hNL, hη, rfl⟩ μ
  obtain ⟨μL⟩ := exists_haarMeasure F L
  rw [value_induce_characterClass F hsys E L h ψ μ μL, fieldDeterminant_induce_characterClass F
    hsys.1 E L h η γ]
  have hr := hrank L h η hNL hη μL
  rw [← hsys.2.2.2.2, ← hsys.2.2.2.2] at hr
  have hu : ε L (traceCharacter F E L h ψ) μL (characterClass F e L
      (restrictCharacter F e E L h χ *
        CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)) =
      CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η (E.unitsInclusion L h γ) *
        ε L (traceCharacter F E L h ψ) μL
          (characterClass F e L (restrictCharacter F e E L h χ)) := by
    apply Units.ext
    rw [Units.val_mul]
    exact hr
  rw [hu, mul_inv_cancel_right]

/-- The same reduction for the relation up to roots of unity of `p`-power order. -/
theorem approximateWitnessOn_characterClass {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (hNI : N ≤ CommonClosureWeilDeligne.inertia F E)
    (ψ : AdditiveCharacter F E) (χ : FieldCharacter F E) (γ : E.fieldˣ)
    (hrank : ∀ (L : Extension F) (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ)
      (hNL : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L),
      (∀ n : N, η ⟨((n : weilSubgroup F E) : localWeilGroup F), hNL n n.2⟩ = 1) →
      ∀ μL : HaarMeasure F L, ∃ k : ℕ,
        (fieldData F L).abelianEpsilonExpression
            (restrictCharacter F e E L h χ *
              CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)
            (traceCharacter F E L h ψ) μL ^ (p ^ k) =
          ((CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η
              (E.unitsInclusion L h γ) : ℂ) *
            (fieldData F L).abelianEpsilonExpression (restrictCharacter F e E L h χ)
              (traceCharacter F E L h ψ) μL) ^ (p ^ k)) :
    ApproximateWitnessOn F e ε E N ψ (characterClass F e E χ) γ := by
  apply approximateWitnessOn_of_span hsys.2.1
    (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)
    (fun w hw hw0 => weilRelativeDegreeZeroBrauer F E N hN hNI w hw hw0)
  rintro y ⟨L, h, η, hNL, hη, rfl⟩ μ
  obtain ⟨μL⟩ := exists_haarMeasure F L
  obtain ⟨k, hr⟩ := hrank L h η hNL hη μL
  refine ⟨k, ?_⟩
  rw [value_induce_characterClass F hsys E L h ψ μ μL, fieldDeterminant_induce_characterClass F
    hsys.1 E L h η γ]
  rw [← hsys.2.2.2.2, ← hsys.2.2.2.2] at hr
  have hu : ε L (traceCharacter F E L h ψ) μL (characterClass F e L
      (restrictCharacter F e E L h χ *
        CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)) ^ (p ^ k) =
      (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η (E.unitsInclusion L h γ) *
        ε L (traceCharacter F E L h ψ) μL
          (characterClass F e L (restrictCharacter F e E L h χ))) ^ (p ^ k) := by
    apply Units.ext
    push_cast
    exact hr
  rw [mul_pow, inv_pow, hu, mul_pow, mul_inv_cancel_right]

/-! ## Translation from the bottom field to the target's witnesses -/

open LocalWeil.Ramification Ramification.Padic LocalClassField

theorem upperGroup_normal (r : ℝ) : (upperGroup F r).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem baseUpperGroup_normal (r : ℝ) : (baseUpperGroup F r).Normal :=
  Subgroup.Normal.comap (upperGroup_normal F r) _

/-- With the inertia comparison, the upper group of index `r ≥ 0` consists of
degree-zero elements, hence lies in the inertia subgroup of the bottom field. -/
theorem baseUpperGroup_le_inertia (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    {r : ℝ} (hr : 0 ≤ r) :
    baseUpperGroup F r ≤ CommonClosureWeilDeligne.inertia F (baseExtension F) := by
  intro g hg
  have h0 : (g : localWeilGroup F) ∈ upperGroup F 0 := upperGroup_antitone F hr hg
  have hI : (g : localWeilGroup F) ∈ localInertia F := by
    rw [localInertia_eq_comap]
    change localProjection F g ∈ F.absoluteInertia F.canonicalTopologicalData
    rw [← hinert]
    exact h0
  exact hI

/-- A generator whose label is below `r` realizes at the bottom field to the
class of a representation trivial on the upper group of index `r`. -/
theorem realizeAtBase_generator_mem
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (b : LocalWeil.Basis.{uF, max uF uV} F) {r : ℝ} (hb : breakLabel F b < r) :
    realizeAtBase.{uF, uV} F (generator b) ∈
      weilTrivialOnSpan.{uF, uV} F (baseExtension F) (baseUpperGroup F r) := by
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    have hlt : lastBreak F A.val < r := hb
    obtain ⟨t, ht, htr⟩ := exists_lt_of_csInf_lt (hthr A.val A.property.1) hlt
    have htriv := isTrivialAt_mono F A.val htr.le ht.2
    have hc' : A.val.rank = (n : ℕ) := hc
    have hgen : generator (⟨n, ⟨Quotient.mk _ A, hc⟩⟩ : LocalWeil.Basis.{uF, max uF uV} F) =
        LocalWeil.ofRepresentation A.val A.property.1 A.property.2 n hc' := rfl
    rw [hgen]
    unfold realizeAtBase
    rw [LinearMap.comp_apply, LocalWeil.realizeExact_ofRepresentation]
    unfold ExactGrothendieckGroup.continuousRestrict
    rw [ExactGrothendieckGroup.restrict_ofRepresentation]
    apply Submodule.subset_span
    refine ⟨_, _, ?_, rfl⟩
    intro g hg
    exact htriv _ hg

/-- A lattice element with all labels below `r` realizes at the bottom field
inside the span of representations trivial on the upper group of index `r`. -/
theorem realizeAtBase_mem_weilTrivialOnSpan
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (w : LocalWeil.Lattice.{uF, max uF uV} F) {r : ℝ} (hw : AllBreaksBelow F w r) :
    realizeAtBase.{uF, uV} F w ∈
      weilTrivialOnSpan.{uF, uV} F (baseExtension F) (baseUpperGroup F r) := by
  induction w using Finsupp.induction with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | single_add b n f hb hn ih =>
    have hb' : breakLabel F b < r := by
      apply hw b
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hb,
        add_zero]
      exact hn
    have hf : AllBreaksBelow F f r := by
      intro c hc
      have hcb : c ≠ b := fun h => hb (h ▸ Finsupp.mem_support_iff.mpr hc)
      apply hw c
      rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hcb, zero_add]
    have hsingle : Finsupp.single b n = n • generator b := by
      simp [generator]
    rw [map_add, hsingle, map_zsmul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ n (realizeAtBase_generator_mem F hthr b hb'))
      (ih hf)

theorem realizeAtBase_mem_degreeZero (w : LocalWeil.Lattice.{uF, max uF uV} F)
    (hw : LocalWeil.degree F w = 0) :
    realizeAtBase.{uF, uV} F w ∈ DegreeZero.{uF, uV} F (baseExtension F) := by
  rw [ExactGrothendieckGroup.mem_degreeZero]
  change degree F (baseExtension F) (realizeAtBase F w) = 0
  rw [degree_realizeAtBase, hw]

/-- The target's exact witness relation follows from the relative one at the
bottom field for the upper group of index `a / 2`. -/
theorem exactWitness_of_exactWitnessOn
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    {v : LocalWeil.Lattice.{uF, max uF uV} F} {a : ℝ}
    {ψ : AdditiveCharacter F (baseExtension F)} {γ : (baseExtension F).fieldˣ}
    (h : ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (a / 2)) ψ
      (realizeAtBase F v) γ) :
    ExactWitness F e ε v a ψ γ := by
  rw [exactWitness_iff]
  intro w hw0 hwb μ
  exact h _ (realizeAtBase_mem_weilTrivialOnSpan F hthr w hwb)
    (realizeAtBase_mem_degreeZero F w hw0) μ

/-- The same translation for the relation up to roots of unity of `p`-power order,
for the upper group of index `a`. -/
theorem approximateWitness_of_approximateWitnessOn
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    {v : LocalWeil.Lattice.{uF, max uF uV} F} {a : ℝ}
    {ψ : AdditiveCharacter F (baseExtension F)} {γ : (baseExtension F).fieldˣ}
    (h : ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F a) ψ
      (realizeAtBase F v) γ) :
    ApproximateWitness F e ε v a ψ γ := by
  rw [approximateWitness_iff]
  intro w hw0 hwb μ
  exact h _ (realizeAtBase_mem_weilTrivialOnSpan F hthr w hwb)
    (realizeAtBase_mem_degreeZero F w hw0) μ

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
