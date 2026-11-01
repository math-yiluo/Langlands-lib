import Langlands.Algebra.NonUnitalBimoduleTensorScalars

/-!
# Interface and boundary checks for compatible tensor residual actions

The complete unapplied types, competing named module structures, and nonzero
regular integer case of the internal coefficient-compatible construction.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalBimoduleTensorScalarsChecks

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)
open NonUnitalBimoduleTensorScalars

universe uk uS uR uX uY

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

noncomputable section

section IndependentUniverses

/-- Complete unapplied type of the per-element linear refinement. -/
example : ∀ (k : Type uk) {S : Type uS} {R : Type uR}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) (_s : S),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    Module.End k (Tensor R X Y) := @linearEnd

/-- Complete unapplied type of the actual nonunital algebra homomorphism. -/
example : ∀ (k : Type uk) {S : Type uS} {R : Type uR}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    S →ₙₐ[k] Module.End k (Tensor R X Y) := @action

/-- Complete unapplied type of equality of the two actual coefficient Modules. -/
example : ∀ (k : Type uk) {S : Type uS} {R : Type uR}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (hX : ActionsCommute S R X)
    (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    [IsScalarTower k S S] [SMulCommClass k S S]
    (hS : IsIdempotented S) (hSX : IsNondegenerate S X)
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    NondegenerateScalars.module k hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y) =
      NondegenerateTensorScalars.module k R X Y hR hY := @recoveredModule_eq

end IndependentUniverses

section UniversesZeroOneTwoThreeFour

/-- Complete unapplied type of the per-element linear refinement. -/
example : ∀ (k : Type 0) {S : Type 1} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 3} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type 4) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) (_s : S),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    Module.End k (Tensor R X Y) := @linearEnd

/-- Complete unapplied type of the actual nonunital algebra homomorphism. -/
example : ∀ (k : Type 0) {S : Type 1} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 3} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type 4) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    S →ₙₐ[k] Module.End k (Tensor R X Y) := @action

/-- Complete unapplied type of equality of the two actual coefficient Modules. -/
example : ∀ (k : Type 0) {S : Type 1} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 3} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (hX : ActionsCommute S R X)
    (Y : Type 4) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    [IsScalarTower k S S] [SMulCommClass k S S]
    (hS : IsIdempotented S) (hSX : IsNondegenerate S X)
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    NondegenerateScalars.module k hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y) =
      NondegenerateTensorScalars.module k R X Y hR hY := @recoveredModule_eq

end UniversesZeroOneTwoThreeFour

section UniversesFourThreeTwoOneZero

/-- Complete unapplied type of the per-element linear refinement. -/
example : ∀ (k : Type 4) {S : Type 3} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type 0) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) (_s : S),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    Module.End k (Tensor R X Y) := @linearEnd

/-- Complete unapplied type of the actual nonunital algebra homomorphism. -/
example : ∀ (k : Type 4) {S : Type 3} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (_hX : ActionsCommute S R X)
    (Y : Type 0) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    S →ₙₐ[k] Module.End k (Tensor R X Y) := @action

/-- Complete unapplied type of equality of the two actual coefficient Modules. -/
example : ∀ (k : Type 4) {S : Type 3} {R : Type 2}
    [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hR : IsIdempotented R) (hX : ActionsCommute S R X)
    (Y : Type 0) [AddCommGroup Y] [NonUnitalModule R Y]
    (hY : IsNondegenerate R Y) [Module k S]
    [IsScalarTower k S S] [SMulCommClass k S S]
    (hS : IsIdempotented S) (hSX : IsNondegenerate S X)
    (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (_hcompat : letI := NondegenerateScalars.module k hR.op hRX; IsScalarTower k S X),
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    NondegenerateScalars.module k hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y) =
      NondegenerateTensorScalars.module k R X Y hR hY := @recoveredModule_eq

end UniversesFourThreeTwoOneZero

section CompetingModules

variable (k : Type uk) {S : Type uS} {R : Type uR}
  [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
  [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hS : IsIdempotented S) (hR : IsIdempotented R) (hX : ActionsCommute S R X)
  (hSX : IsNondegenerate S X) (hRX : IsNondegenerate Rᵐᵒᵖ X)
  (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y] (hY : IsNondegenerate R Y)
  [competingX : Module k X] [competingY : Module k Y]
  [competingT : Module k (Tensor R X Y)]
  [competingHS : NonUnitalModule S (Tensor R X Y)]

local notation "MX" => NondegenerateScalars.module k hR.op hRX
local notation "MY" => NondegenerateScalars.module k hR hY
local notation "MT" => NondegenerateTensorScalars.module k R X Y hR hY
local notation "HS" => NonUnitalBimoduleTensor.leftModule hX Y

/-- Local selections pin all four structures even when competing ones are available. -/
example :
    letI := MX
    letI := MY
    letI := MT
    letI := HS
    (inferInstance : Module k X) = MX ∧
      (inferInstance : Module k Y) = MY ∧
      (inferInstance : Module k (Tensor R X Y)) = MT ∧
      (inferInstance : NonUnitalModule S (Tensor R X Y)) = HS :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The input law selects MX explicitly, and the output has exactly MT and HS. -/
example (hcompat : letI := MX; IsScalarTower k S X) (c : k) (s : S)
    (t : Tensor R X Y) (x : X) (y : Y) :
    letI := MX
    letI := MY
    letI := MT
    letI := HS
    IsScalarTower k S (Tensor R X Y) ∧
      SMulCommClass k S (Tensor R X Y) ∧
      (c • s) • t = c • (s • t) ∧
      s • (c • t) = c • (s • t) ∧
      action k hR hX Y hY hRX hcompat s (tmul R X Y x y) = tmul R X Y (s • x) y :=
  ⟨isScalarTower k hR hX Y hY hRX hcompat,
    smulCommClass k hR hX Y hY,
    scalar_action k hR hX Y hY hRX hcompat c s t,
    action_smul k hR hX Y hY c s t,
    action_tmul k hR hX Y hY hRX hcompat s x y⟩

/-- The Module comparison still refers to the exact original residual action. -/
example (hcompat : letI := MX; IsScalarTower k S X) :
    letI := MX
    letI := MY
    letI := MT
    letI := HS
    NonUnitalModule.ofLinearEndHom (action k hR hX Y hY hRX hcompat) = HS ∧
      NondegenerateScalars.module k hS
          (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y) = MT :=
  ⟨ofLinearEndHom_action k hR hX Y hY hRX hcompat,
    recoveredModule_eq k hR hX Y hY hS hSX hRX hcompat⟩

/-- Both factor formulas use the named recovered coefficients, under the same competitors. -/
example (c : k) (x : X) (y : Y) :
    letI := MX
    letI := MY
    letI := MT
    c • tmul R X Y x y = tmul R X Y (c • x) y ∧
      c • tmul R X Y x y = tmul R X Y x (c • y) :=
  ⟨NondegenerateTensorScalars.smul_tmul_left k R X Y hR hRX hY c x y,
    NondegenerateTensorScalars.smul_tmul_right k R X Y hR hY c x y⟩

end CompetingModules

section RegularInteger

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private theorem integerLeftNondegenerate : IsNondegenerate ℤ ℤ :=
  NondegenerateTensorFunctor.regular_isNondegenerate (IsIdempotented.of_ring ℤ)

private theorem integerRightNondegenerate : IsNondegenerate ℤᵐᵒᵖ ℤ :=
  NondegenerateTensorFunctor.rightRegular_isNondegenerate (IsIdempotented.of_ring ℤ)

private theorem integerCompatible :
    InputCompatible ℤ (S := ℤ) (IsIdempotented.of_ring ℤ) integerRightNondegenerate := by
  refine (inputCompatible_iff ℤ (S := ℤ)
    (IsIdempotented.of_ring ℤ) integerRightNondegenerate).2 ?_
  intro c s x
  change (c * s) * x = NondegenerateScalars.scalarMul ℤ integerRightNondegenerate c (s * x)
  have hm : NondegenerateTensorScalars.rightModule ℤ
      (IsIdempotented.of_ring ℤ) integerRightNondegenerate = (inferInstance : Module ℤ ℤ) :=
    Subsingleton.elim _ _
  have hc := congrArg (fun m : Module ℤ ℤ => m.toSMul.smul c (s * x)) hm
  change NondegenerateScalars.scalarMul ℤ integerRightNondegenerate c (s * x) = c * (s * x) at hc
  rw [hc]
  exact mul_assoc c s x

private def integerPairing : ℤ →+ ℤ →+ ℤ where
  toFun x :=
    { toFun y := x * y
      map_zero' := mul_zero x
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext zero_mul
  map_add' x x' := AddMonoidHom.ext fun y => add_mul x x' y

private theorem integerPairing_balanced : NonUnitalModuleTensor.IsBalanced ℤ integerPairing :=
  fun a x y => mul_assoc x a y

private theorem integerTensor_two_ne_zero : tmul ℤ ℤ ℤ 2 1 ≠ 0 := by
  intro h
  have hh := congrArg (NonUnitalModuleTensor.lift ℤ integerPairing integerPairing_balanced) h
  change (2 : ℤ) * 1 = 0 at hh
  norm_num at hh

/-- The actual bundled action sends 1⊗1 to 2⊗1, which is nonzero. -/
example :
    letI := NondegenerateTensorScalars.module ℤ ℤ ℤ ℤ
      (IsIdempotented.of_ring ℤ) integerLeftNondegenerate
    letI := NonUnitalBimoduleTensor.leftModule (NonUnitalModule.regular_actionsCommute ℤ) ℤ
    action ℤ (IsIdempotented.of_ring ℤ) (NonUnitalModule.regular_actionsCommute ℤ) ℤ
        integerLeftNondegenerate integerRightNondegenerate integerCompatible 2
        (tmul ℤ ℤ ℤ 1 1) = tmul ℤ ℤ ℤ 2 1 ∧
      (2 : ℤ) • tmul ℤ ℤ ℤ 1 1 = tmul ℤ ℤ ℤ 2 1 ∧
      tmul ℤ ℤ ℤ 2 1 ≠ 0 :=
  ⟨rfl, rfl, integerTensor_two_ne_zero⟩

end RegularInteger

end

end Langlands.Algebra.NonUnitalBimoduleTensorScalarsChecks
