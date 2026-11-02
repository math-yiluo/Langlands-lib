import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.Rational.Characters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Pi

/-! # The actual normalized logarithmic character map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The real dual `Hom_Z(Rat(G), ℝ)` of the actual rational-character group. -/
def RealCharacterDual := GroupScheme.rationalCharacters G →+ ℝ
  deriving AddCommGroup, FunLike

instance : Module ℝ (RealCharacterDual F G) :=
  inferInstanceAs (Module ℝ (GroupScheme.rationalCharacters G →+ ℝ))

/-- Pointwise convergence on actual rational characters. -/
instance : TopologicalSpace (RealCharacterDual F G) :=
  TopologicalSpace.induced (fun ℓ : RealCharacterDual F G => fun χ => ℓ χ) inferInstance

/-- Evaluation of a real dual element at an actual rational character. -/
def dualEval (χ : GroupScheme.rationalCharacters G) : RealCharacterDual F G →ₗ[ℝ] ℝ where
  toFun ℓ := ℓ χ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField F] in
theorem continuous_dualEval (χ : GroupScheme.rationalCharacters G) :
    Continuous (dualEval F G χ) :=
  (continuous_apply χ).comp continuous_induced_dom

instance : T2Space (RealCharacterDual F G) :=
  T2Space.of_injective_continuous
    (fun {_ _} h => AddMonoidHom.ext (congrFun h))
    (continuous_induced_dom :
      Continuous (fun ℓ : RealCharacterDual F G => fun χ => ℓ χ))

instance : IsTopologicalAddGroup (RealCharacterDual F G) where
  continuous_add := continuous_induced_rng.mpr (continuous_pi fun χ =>
    ((continuous_dualEval F G χ).comp continuous_fst).add
      ((continuous_dualEval F G χ).comp continuous_snd))
  continuous_neg := continuous_induced_rng.mpr (continuous_pi fun χ =>
    (continuous_dualEval F G χ).neg)

instance : UniformSpace (RealCharacterDual F G) :=
  IsTopologicalAddGroup.rightUniformSpace (RealCharacterDual F G)

instance : IsUniformAddGroup (RealCharacterDual F G) :=
  isUniformAddGroup_of_addCommGroup

instance : ContinuousSMul ℝ (RealCharacterDual F G) where
  continuous_smul := continuous_induced_rng.mpr (continuous_pi fun χ =>
    continuous_fst.smul ((continuous_dualEval F G χ).comp continuous_snd))

omit [NumberField F] in
/-- Evaluation of an additive sum of actual characters is multiplication of units. -/
theorem characterUnits_add (χ ψ : GroupScheme.rationalCharacters G)
    (A : CommAlgCat.{u} (CommRingCat.of F)) (x : G.affinePoints A) :
    characterUnits F G (χ + ψ).toMul A x =
      characterUnits F G χ.toMul A x * characterUnits F G ψ.toMul A x := by
  have h := congrArg Additive.toMul
    ((GroupScheme.evalHom G (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp
      ((algSpec (CommRingCat.of F)).obj (Opposite.op A)) x).map_add χ ψ)
  change x ≫ (χ + ψ).toMul.hom.hom =
    (x ≫ χ.toMul.hom.hom) * (x ≫ ψ.toMul.hom.hom) at h
  change GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) A
    (x ≫ (χ + ψ).toMul.hom.hom) = _
  rw [h, map_mul]
  rfl

omit [NumberField F] in
/-- The zero rational character evaluates to the unit. -/
@[simp] theorem characterUnits_zero
    (A : CommAlgCat.{u} (CommRingCat.of F)) (x : G.affinePoints A) :
    characterUnits F G (0 : GroupScheme.rationalCharacters G).toMul A x = 1 := by
  have h := congrArg Additive.toMul
    (GroupScheme.evalHom G (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp
      ((algSpec (CommRingCat.of F)).obj (Opposite.op A)) x).map_zero
  change x ≫ (0 : GroupScheme.rationalCharacters G).toMul.hom.hom = 1 at h
  change GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) A
    (x ≫ (0 : GroupScheme.rationalCharacters G).toMul.hom.hom) = 1
  rw [h, map_one]

/-- Actual normalized character norms respect addition of rational characters. -/
theorem characterNorm_add (χ ψ : GroupScheme.rationalCharacters G) (x : AdelicGroupPoints F G) :
    characterNorm F G (χ + ψ).toMul x =
      characterNorm F G χ.toMul x * characterNorm F G ψ.toMul x := by
  change IdeleAbsoluteValue.full F (characterUnits F G (χ + ψ).toMul _ x) = _
  rw [characterUnits_add, map_mul]
  rfl

@[simp] theorem characterNorm_zero (x : AdelicGroupPoints F G) :
    characterNorm F G (0 : GroupScheme.rationalCharacters G).toMul x = 1 := by
  change IdeleAbsoluteValue.full F (characterUnits F G (0 : GroupScheme.rationalCharacters G).toMul _ x) = 1
  rw [characterUnits_zero, map_one]

/-- The normalized logarithmic functional of an actual adelic point. -/
def characterLog (x : AdelicGroupPoints F G) : RealCharacterDual F G where
  toFun χ := Real.log ((characterNorm F G χ.toMul x : ℝ≥0) : ℝ)
  map_zero' := by
    rw [characterNorm_zero]
    exact Real.log_one
  map_add' χ ψ := by
    rw [characterNorm_add, Units.val_mul, NNReal.coe_mul, Real.log_mul]
    · exact_mod_cast (characterNorm F G χ.toMul x).ne_zero
    · exact_mod_cast (characterNorm F G ψ.toMul x).ne_zero

@[simp] theorem characterLog_apply (x : AdelicGroupPoints F G) (χ : GroupScheme.rationalCharacters G) :
    characterLog F G x χ = Real.log ((characterNorm F G χ.toMul x : ℝ≥0) : ℝ) := rfl

@[simp] theorem characterLog_one : characterLog F G 1 = 0 := by
  apply AddMonoidHom.ext
  intro χ
  change Real.log ((characterNorm F G χ.toMul 1 : ℝ≥0) : ℝ) = 0
  rw [map_one]
  exact Real.log_one

/-- Multiplication of actual adelic points becomes addition in the real dual. -/
theorem characterLog_mul (x y : AdelicGroupPoints F G) :
    characterLog F G (x * y) = characterLog F G x + characterLog F G y := by
  apply AddMonoidHom.ext
  intro χ
  change Real.log ((characterNorm F G χ.toMul (x * y) : ℝ≥0) : ℝ) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul]
  · rfl
  · exact_mod_cast (characterNorm F G χ.toMul x).ne_zero
  · exact_mod_cast (characterNorm F G χ.toMul y).ne_zero

/-- The kernel is exactly the existing actual norm-one subgroup. -/
theorem characterLog_eq_zero_iff (x : AdelicGroupPoints F G) :
    characterLog F G x = 0 ↔ x ∈ normOneSubgroup F G := by
  constructor
  · intro hx
    apply (mem_normOneSubgroup F G x).mpr
    intro χ
    have h := DFunLike.congr_fun hx (Additive.ofMul χ)
    have hp : 0 < ((characterNorm F G χ x : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (characterNorm F G χ x).ne_zero)
    apply Units.ext
    apply NNReal.eq
    exact Real.eq_one_of_pos_of_log_eq_zero hp h
  · intro hx
    apply AddMonoidHom.ext
    intro χ
    change Real.log ((characterNorm F G χ.toMul x : ℝ≥0) : ℝ) = 0
    rw [(mem_normOneSubgroup F G x).mp hx χ.toMul]
    exact Real.log_one

@[simp] theorem characterLog_rational (x : RationalGroupPoints F G) :
    characterLog F G (rational F G x) = 0 :=
  (characterLog_eq_zero_iff F G _).mpr
    (rationalSubgroup_le_normOneSubgroup F G ⟨x, rfl⟩)

/-- The actual log map is zero on every compact adelic subgroup. -/
theorem characterLog_eq_zero_on_compactSubgroup
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
    {x : AdelicGroupPoints F G} (hx : x ∈ K) : characterLog F G x = 0 :=
  (characterLog_eq_zero_iff F G x).mpr (compactSubgroup_le_normOneSubgroup F G K hK hx)

/-- Every character coordinate of the actual logarithmic map is continuous. -/
theorem continuous_characterLog_eval (χ : GroupScheme.rationalCharacters G) :
    Continuous (fun x : AdelicGroupPoints F G => characterLog F G x χ) := by
  apply (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (characterNorm F G χ.toMul).continuous)).log
  intro x
  change ((characterNorm F G χ.toMul x : ℝ≥0) : ℝ) ≠ 0
  exact_mod_cast (characterNorm F G χ.toMul x).ne_zero

/-- Continuity for the topology of pointwise convergence on actual rational characters. -/
theorem continuous_characterLog : Continuous (characterLog F G) :=
  continuous_induced_rng.mpr (continuous_pi fun χ => continuous_characterLog_eval F G χ)

/-- The actual logarithmic map bundled as a continuous homomorphism. -/
def characterLogHom : AdelicGroupPoints F G →ₜ* Multiplicative (RealCharacterDual F G) where
  toFun x := Multiplicative.ofAdd (characterLog F G x)
  map_one' := characterLog_one F G
  map_mul' := characterLog_mul F G
  continuous_toFun := continuous_characterLog F G

/-- The kernel of the bundled map is the same actual norm-one subgroup. -/
theorem characterLogHom_ker :
    (characterLogHom F G).toMonoidHom.ker = normOneSubgroup F G := by
  ext x
  exact characterLog_eq_zero_iff F G x

variable (H : GroupScheme (Spec (CommRingCat.of F)))

/-- The induced real-linear covariant map of actual character duals. -/
def realCharacterDualMap (f : G ⟶ H) : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F H where
  toFun ℓ := ℓ.comp (GroupScheme.characterRestrict f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField F] in
theorem continuous_realCharacterDualMap (f : G ⟶ H) :
    Continuous (realCharacterDualMap F G H f) :=
  continuous_induced_rng.mpr
    (continuous_pi fun χ => continuous_dualEval F G (GroupScheme.characterRestrict f χ))

/-- The normalized logarithmic map commutes with actual group-scheme morphisms. -/
theorem characterLog_map (f : G ⟶ H) (x : AdelicGroupPoints F G) :
    characterLog F H (map F G H f x) = realCharacterDualMap F G H f (characterLog F G x) := by
  apply AddMonoidHom.ext
  intro χ
  change Real.log ((characterNorm F H χ.toMul (map F G H f x) : ℝ≥0) : ℝ) =
    Real.log ((characterNorm F G (f ≫ χ.toMul) x : ℝ≥0) : ℝ)
  rw [characterNorm_comp]

end Langlands.Global.AdelicGroupPoints
