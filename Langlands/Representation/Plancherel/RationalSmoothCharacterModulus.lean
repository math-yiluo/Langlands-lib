import Langlands.Representation.Plancherel.RationalSmoothRealDescentConstruction
import Langlands.Representation.Plancherel.UnramifiedLogarithm
import Mathlib.Analysis.Normed.Field.Basic

/-! # Smooth complex characters and the actual rational norm kernel -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.RationalPoints
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG

section Character

variable {G : Type uG} [Group G]

/-- The normalized logarithm of the modulus of an arbitrary complex character.
The multiplicative tag records addition of the real logarithms. -/
def complexCharacterLogModulus (q : ℝ) (θ : G →* ℂˣ) :
    G →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd
    (normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ g)))
  map_one' := by
    change normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ 1)) = 0
    rw [map_one, map_one, normLog_one]
  map_mul' g h := by
    change normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ (g * h))) =
      normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ g)) +
      normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ h))
    rw [map_mul, map_mul, normLog_mul]

@[simp]
theorem complexCharacterLogModulus_apply (q : ℝ) (θ : G →* ℂˣ) (g : G) :
    (complexCharacterLogModulus q θ g).toAdd =
      -Real.log ‖(θ g : ℂ)‖ / Real.log q := rfl

/-- For a base greater than one, vanishing logarithmic modulus is exactly
the norm-one condition. -/
theorem complexCharacterLogModulus_eq_one_iff {q : ℝ} (hq : 1 < q)
    (θ : G →* ℂˣ) (g : G) :
    complexCharacterLogModulus q θ g = 1 ↔ ‖(θ g : ℂ)‖ = 1 := by
  change normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ g)) = 0 ↔ _
  rw [normLog_eq_zero_iff hq]
  constructor
  · intro h
    exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) h
  · intro h
    apply Units.ext
    apply NNReal.eq
    exact h

/-- A character's kernel is contained in its logarithmic-modulus kernel. -/
theorem ker_le_complexCharacterLogModulus_ker (q : ℝ) (θ : G →* ℂˣ) :
    θ.ker ≤ (complexCharacterLogModulus q θ).ker := by
  intro g hg
  change θ g = 1 at hg
  change normLog q (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (θ g)) = 0
  rw [hg, map_one, normLog_one]

/-- Smoothness in the open-kernel sense passes to logarithmic modulus. -/
theorem isOpen_ker_complexCharacterLogModulus [TopologicalSpace G]
    [SeparatelyContinuousMul G] (q : ℝ) (θ : G →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set G)) :
    IsOpen ((complexCharacterLogModulus q θ).ker : Set G) :=
  Subgroup.isOpen_mono (ker_le_complexCharacterLogModulus_ker q θ) hθ

end Character

section RationalPoints

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M)

/-- Conditional norm-kernel unitarity of every smooth complex character.
All three actual local-point prerequisites remain explicit hypotheses. -/
theorem norm_eq_one_on_rationalCommonNormKernel_of_structure
    (hcompact : CentralNormKernelCompactness M hM)
    (hcocompact : CentralDerivedNormKernelCocompactness M hM)
    (hderived : DerivedSmoothRealAnnihilation M hM) :
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    ∀ (θ : GroupScheme.rationalPoints M →* ℂˣ),
      IsOpen (θ.ker : Set (GroupScheme.rationalPoints M)) →
      ∀ g ∈ rationalCommonNormKernel M, ‖(θ g : ℂ)‖ = 1 := by
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : Smooth M.X.hom := hM.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  let : IsTopologicalGroup (GroupScheme.rationalPoints M) :=
    rationalPoint_isTopologicalGroup F M
  intro θ hθ g hg
  have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hker := rationalCommonNormKernel_le_ker_of_structure M hM
    hcompact hcocompact hderived
    (complexCharacterLogModulus (LocalField.residueCardinality F) θ)
    (isOpen_ker_complexCharacterLogModulus _ θ hθ)
  exact (complexCharacterLogModulus_eq_one_iff hq θ g).mp (hker hg)

end RationalPoints

end Langlands.Plancherel
