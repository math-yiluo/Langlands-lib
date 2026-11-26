import Langlands.GroupScheme.Dilatation.GroupModel
import Langlands.GroupScheme.IntegralModel.CongruenceTower

/-! # The congruence group schemes of an integral model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Dilatation

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) {ϖ : R} (hϖ : Irreducible ϖ)

include hϖ in
/-- The power of the chosen uniformizer generates the original maximal-ideal power. -/
theorem maximalIdeal_pow_eq_span (n : ℕ) :
    IsLocalRing.maximalIdeal R ^ n = Ideal.span {ϖ ^ n} := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

private theorem isClosedImmersion_congruenceUnit (n : ℕ+) :
    IsClosedImmersion (kernelUnit (M.congruenceFibre n)).hom.hom.left := by
  let : IsAffineHom (M.congruenceFibre n).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd M.group.X.hom (congruenceBaseMap R n)))
  let : IsSeparated (M.congruenceFibre n).X.hom := IsSeparated.of_isAffineHom _
  exact kernelUnit_isClosedSubgroup _

/-- The positive congruence model is the single affine dilatation of the unit
in the model over the actual congruence quotient. -/
def positiveCongruenceModel (n : ℕ+) : IntegralModel R K G :=
  letI := isClosedImmersion_congruenceUnit M n
  M.dilatationAtQuotient (pow_ne_zero (n : ℕ) hϖ.ne_zero) (maximalIdeal_pow_eq_span hϖ n)
    (kernelUnit (M.congruenceFibre n))

/-- The structural map of the positive congruence model into the original model. -/
def positiveCongruenceModelHom (n : ℕ+) : (M.positiveCongruenceModel hϖ n).Hom M (𝟙 G) :=
  letI := isClosedImmersion_congruenceUnit M n
  M.dilatationAtQuotientHom (pow_ne_zero (n : ℕ) hϖ.ne_zero) (maximalIdeal_pow_eq_span hϖ n)
    (kernelUnit (M.congruenceFibre n))

/-- The `n`th congruence group scheme with its original prescribed generic fibre. -/
def congruenceModel (n : ℕ) : IntegralModel R K G :=
  match n with
  | 0 => M
  | n + 1 => M.positiveCongruenceModel hϖ ⟨n + 1, Nat.succ_pos n⟩

/-- Its structural map extends the identity on the supplied generic group. -/
def congruenceModelHom (n : ℕ) : (M.congruenceModel hϖ n).Hom M (𝟙 G) :=
  match n with
  | 0 => ⟨𝟙 M.group, by
      change (baseChange (Spec.algebraMap R K)).map (𝟙 M.group) ≫ M.genericIso.hom =
        M.genericIso.hom ≫ 𝟙 G
      simp⟩
  | n + 1 => M.positiveCongruenceModelHom hϖ ⟨n + 1, Nat.succ_pos n⟩

@[simp] theorem congruenceModel_zero : M.congruenceModel hϖ 0 = M := rfl

@[simp] theorem congruenceModelHom_zero : (M.congruenceModelHom hϖ 0).hom = 𝟙 M.group := rfl

/-- The finite-type model at a positive natural level is the positive-level construction. -/
theorem congruenceModel_coe_pnat (n : ℕ+) :
    M.congruenceModel hϖ (n : ℕ) = M.positiveCongruenceModel hϖ n := by
  rcases n with ⟨_ | k, hp⟩
  · exact (Nat.lt_irrefl _ hp).elim
  · rfl

/-- The actual quotient pullback on test points, as a group homomorphism. -/
def congruenceTestReduction (n : ℕ+) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ M.group.X) →*
      ((Over.pullback (congruenceBaseMap R n)).obj T ⟶ (M.congruenceFibre n).X) :=
  (Over.pullback (congruenceBaseMap R n)).homMonoidHom

/-- A point on a flat affine test has a unique lift to the positive congruence model
exactly when its reduction is the identity on the actual quotient-base test. -/
theorem positiveCongruenceModel_lift_iff (n : ℕ+) {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [Flat T.hom] (x : T ⟶ M.group.X) :
    (∃! y : T ⟶ (M.positiveCongruenceModel hϖ n).group.X,
      y ≫ (M.positiveCongruenceModelHom hϖ n).hom.hom.hom = x) ↔
      M.congruenceTestReduction n T x = 1 := by
  let : IsClosedImmersion (kernelUnit (M.congruenceFibre n)).hom.hom.left :=
    isClosedImmersion_congruenceUnit M n
  simp only [positiveCongruenceModel, positiveCongruenceModelHom]
  rw [M.dilatationAtQuotient_lift_iff (pow_ne_zero (n : ℕ) hϖ.ne_zero)
    (maximalIdeal_pow_eq_span hϖ n) (kernelUnit (M.congruenceFibre n)) x]
  constructor
  · rintro ⟨y, hy⟩
    change y ≫ η[(M.congruenceFibre n).X] = M.congruenceTestReduction n T x at hy
    rw [← hy]
    change y ≫ η[(M.congruenceFibre n).X] = 1
    rw [toUnit_unique y (toUnit _)]
    rfl
  · intro hx
    exact ⟨toUnit _, hx.symm⟩

/-- The same lifting criterion for the natural-number tower at a positive level. -/
theorem congruenceModel_lift_iff (n : ℕ+) {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [Flat T.hom] (x : T ⟶ M.group.X) :
    (∃! y : T ⟶ (M.congruenceModel hϖ (n : ℕ)).group.X,
      y ≫ (M.congruenceModelHom hϖ (n : ℕ)).hom.hom.hom = x) ↔
      M.congruenceTestReduction n T x = 1 := by
  rcases n with ⟨_ | k, hp⟩
  · exact (Nat.lt_irrefl _ hp).elim
  · exact M.positiveCongruenceModel_lift_iff hϖ ⟨k + 1, hp⟩ x

/-- Image inside the actual integral sections of the original model. -/
theorem range_positiveCongruenceSections (n : ℕ+) :
    (rationalPoints.map (M.positiveCongruenceModelHom hϖ n).hom).range =
      M.congruenceKernelAt n := by
  let : IsClosedImmersion (kernelUnit (M.congruenceFibre n)).hom.hom.left :=
    isClosedImmersion_congruenceUnit M n
  simp only [positiveCongruenceModelHom]
  rw [M.range_dilatationAtQuotientSections (pow_ne_zero (n : ℕ) hϖ.ne_zero)
    (maximalIdeal_pow_eq_span hϖ n) (kernelUnit (M.congruenceFibre n))]
  ext x
  change (∃ y : rationalPoints (Grp.trivial _), y ≫ η[(M.congruenceFibre n).X] =
    M.reductionAt n x) ↔ M.reductionAt n x = 1
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy, toUnit_unique y (toUnit _)]
    rfl
  · intro hx
    exact ⟨toUnit _, hx.symm⟩

/-- The integral sections of the positive congruence model give precisely the existing
congruence subgroup of the supplied generic group. -/
theorem integralPoints_positiveCongruenceModel (n : ℕ+) :
    (M.positiveCongruenceModel hϖ n).integralPoints = M.congruenceSubgroupAt n := by
  let : IsClosedImmersion (kernelUnit (M.congruenceFibre n)).hom.hom.left :=
    isClosedImmersion_congruenceUnit M n
  simp only [positiveCongruenceModel]
  rw [M.integralPoints_dilatationAtQuotient (pow_ne_zero (n : ℕ) hϖ.ne_zero)
    (maximalIdeal_pow_eq_span hϖ n) (kernelUnit (M.congruenceFibre n)),
    ← M.range_dilatationAtQuotientSections (pow_ne_zero (n : ℕ) hϖ.ne_zero)
      (maximalIdeal_pow_eq_span hϖ n) (kernelUnit (M.congruenceFibre n))]
  change (rationalPoints.map (M.positiveCongruenceModelHom hϖ n).hom).range.map
    M.integralPointMap = (M.congruenceKernelAt n).map M.integralPointMap
  rw [M.range_positiveCongruenceSections hϖ n]

/-- Generic integral-point image in the natural-number indexing at any positive level. -/
theorem integralPoints_congruenceModel (n : ℕ+) :
    (M.congruenceModel hϖ (n : ℕ)).integralPoints = M.congruenceSubgroupAt n := by
  rw [M.congruenceModel_coe_pnat, M.integralPoints_positiveCongruenceModel]

end Langlands.GroupScheme.IntegralModel
