import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanPlaceAdjoint

/-! # Operator commutation with the compact factors away from a place -/

noncomputable section

open scoped Classical TensorProduct

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance operatorComplementRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance operatorComplementContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorComplementSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance operatorComplementRing : Ring (automorphicOperatorAlgebra F n) :=
  Subalgebra.toRing _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "K" => ArchimedeanCompactFactors F n
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "toK" => ArchimedeanCompactFactors.toStandardCompact F n
local notation "rK" => ArchimedeanCompactFactors.realPlaceFactor F n
local notation "cK" => ArchimedeanCompactFactors.complexPlaceFactor F n

/-- Compact factors with identity coordinate at the given real place. -/
def RealPlaceCompactComplement (n : ℕ) (v : RP) := {p : ArchimedeanCompactFactors F n // p.1 v = 1}

/-- Compact factors with identity coordinate at the given complex place. -/
def ComplexPlaceCompactComplement (n : ℕ) (v : CP) :=
  {p : ArchimedeanCompactFactors F n // p.2 v = 1}

omit [NumberField F] in
theorem exists_realPlaceCompactComplement (v : RP) (k : standardInfiniteCompact F n) :
    ∃ (p : RealPlaceCompactComplement n v) (l : RK),
      toK p.val * realPlaceCompactInclusion F n v l = k := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  refine ⟨⟨(Function.update p.1 v 1, p.2), Function.update_self v 1 p.1⟩, p.1 v, ?_⟩
  change toK (Function.update p.1 v 1, p.2) * toK (rK v (p.1 v)) = toK p
  rw [← map_mul]
  apply congrArg toK
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change Function.update p.1 v 1 w * (Pi.mulSingle v (p.1 v) : RP → RK) w = p.1 w
    by_cases hw : w = v <;> simp [hw]
  · change p.2 w * 1 = p.2 w
    rw [mul_one]

omit [NumberField F] in
theorem exists_complexPlaceCompactComplement (v : CP) (k : standardInfiniteCompact F n) :
    ∃ (p : ComplexPlaceCompactComplement n v) (l : CK),
      toK p.val * complexPlaceCompactInclusion F n v l = k := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  refine ⟨⟨(p.1, Function.update p.2 v 1), Function.update_self v 1 p.2⟩, p.2 v, ?_⟩
  change toK (p.1, Function.update p.2 v 1) * toK (cK v (p.2 v)) = toK p
  rw [← map_mul]
  apply congrArg toK
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.1 w * 1 = p.1 w
    rw [mul_one]
  · change Function.update p.2 v 1 w * (Pi.mulSingle v (p.2 v) : CP → CK) w = p.2 w
    by_cases hw : w = v <;> simp [hw]

omit [NumberField F] in
theorem realPlaceCompactComplement_commute (v : RP) (p : RealPlaceCompactComplement n v)
    (k : RK) : Commute (toK p.val) (realPlaceCompactInclusion F n v k) := by
  change toK p.val * toK (rK v k) = toK (rK v k) * toK p.val
  rw [← map_mul, ← map_mul]
  apply congrArg toK
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.val.1 w * (Pi.mulSingle v k : RP → RK) w =
      (Pi.mulSingle v k : RP → RK) w * p.val.1 w
    by_cases hw : w = v
    · subst w
      simp [p.property]
    · simp [hw]
  · change p.val.2 w * 1 = 1 * p.val.2 w
    simp

omit [NumberField F] in
theorem complexPlaceCompactComplement_commute (v : CP) (p : ComplexPlaceCompactComplement n v)
    (k : CK) : Commute (toK p.val) (complexPlaceCompactInclusion F n v k) := by
  change toK p.val * toK (cK v k) = toK (cK v k) * toK p.val
  rw [← map_mul, ← map_mul]
  apply congrArg toK
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.val.1 w * 1 = 1 * p.val.1 w
    simp
  · change p.val.2 w * (Pi.mulSingle v k : CP → CK) w =
      (Pi.mulSingle v k : CP → CK) w * p.val.2 w
    by_cases hw : w = v
    · subst w
      simp [p.property]
    · simp [hw]

theorem finiteOperator_compactOperator_commute (g : FiniteAdelicGL F n)
    (k : standardInfiniteCompact F n) :
    Commute (finiteOperator F n g) (compactOperator F n k) := by
  apply Subtype.ext
  change finiteSmoothRightAction F n (AdelicGL.ofFinite F n g) *
      finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) =
    finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) *
      finiteSmoothRightAction F n (AdelicGL.ofFinite F n g)
  rw [← map_mul, ← map_mul, AdelicGL.ofFinite_eq_pair, AdelicGL.ofInfinite_eq_pair,
    AdelicGL.pair_mul, AdelicGL.pair_mul, one_mul, mul_one, one_mul, mul_one]

theorem finiteOperator_differentialOperator_commute (g : FiniteAdelicGL F n)
    (z : EnvelopingAlgebra F n) : Commute (finiteOperator F n g) (differentialOperator F n z) := by
  apply Subtype.ext
  apply LinearMap.ext
  exact finiteSmoothFiniteRightAction_envelopingAction F n g z

theorem compactOperator_differentialOperator_covariance (k : standardInfiniteCompact F n)
    (z : EnvelopingAlgebra F n) :
    compactOperator F n k * differentialOperator F n z =
      differentialOperator F n (envelopingConjugation F n k.val z) * compactOperator F n k := by
  apply Subtype.ext
  apply LinearMap.ext
  exact finiteSmoothRightAction_envelopingAction k.val z

private theorem compactOperator_differentialGenerator_commute (k : standardInfiniteCompact F n)
    (z : ComplexLieAlgebra F n) (h : complexLieConjugation F n k.val z = z) :
    Commute (compactOperator F n k) (differentialOperator F n (envelopingGenerator F n z)) := by
  have h₁ : envelopingConjugation F n k.val (envelopingGenerator F n z) =
      envelopingGenerator F n z :=
    (envelopingConjugation_generator F n k.val z).trans (congrArg (envelopingGenerator F n) h)
  exact (compactOperator_differentialOperator_covariance k (envelopingGenerator F n z)).trans
    (congrArg (fun a => differentialOperator F n a * compactOperator F n k) h₁)

theorem realPlaceCompactComplement_differentialOperator_commute (v : RP)
    (p : RealPlaceCompactComplement n v) (X : RM) :
    Commute (compactOperator F n (toK p.val))
      (differentialOperator F n (envelopingGenerator F n
        (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))) := by
  apply compactOperator_differentialGenerator_commute
  change complexLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p.val)
    (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) = _
  rw [complexLieConjugation_realInclusion, p.property, unitaryMatrixComplexLieConjugation_tmul]
  simp

theorem complexPlaceCompactComplement_differentialOperator_commute (v : CP)
    (p : ComplexPlaceCompactComplement n v) (X : CM) :
    Commute (compactOperator F n (toK p.val))
      (differentialOperator F n (envelopingGenerator F n
        (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))) := by
  apply compactOperator_differentialGenerator_commute
  change complexLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p.val)
    (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) = _
  rw [complexLieConjugation_complexInclusion, p.property, unitaryMatrixComplexLieConjugation_tmul]
  simp

end Langlands.Automorphic
