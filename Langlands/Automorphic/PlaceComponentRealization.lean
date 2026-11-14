import Langlands.Automorphic.PlaceComponentDetection
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceCompactCovariance
import Langlands.Automorphic.CuspidalOperatorRealization
import Langlands.Algebra.LieCasimir

/-!
# Detection at an infinite place of an irreducible operator realization

Let `S` be an irreducible operator realization of `GL_n` over a number field and `v` an
infinite place. This module shows that the free set (`PlaceComponent.freeSet`) of the place
actions at `v` for a matrix representation `τ` of `O(n)` (real `v`) or `U(n)` (complex `v`) is
preserved by the whole concrete operator algebra: finite translations and the compact translations away from `v` commute with the
place actions, the compact translations at `v` and the Lie action at `v` preserve stable
hulls, and the Lie actions at the other places commute with the Lie action at `v`. By
irreducibility the free set is `⊥` as soon as some vector is not free, and then every nonzero
stable subspace has a nonzero `τ`-intertwiner.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false


namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance placeRealizationRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeRealizationContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeRealizationSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeRealizationFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeRealizationStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeRealizationSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-! ### Brackets of distinct place directions -/

omit [NumberField F] in
theorem lie_realPlaceLieInclusion_of_ne {v w : RP} (h : w ≠ v) (X Y : RM) :
    ⁅realPlaceLieInclusion F n v X, realPlaceLieInclusion F n w Y⁆ = 0 := by
  classical
  have h1 : realLiePlaceCoordinates F n
      ⁅realPlaceLieInclusion F n v X, realPlaceLieInclusion F n w Y⁆ = 0 := by
    rw [LieEquiv.map_lie, realLiePlaceCoordinates_realInclusion,
      realLiePlaceCoordinates_realInclusion]
    refine Prod.ext (funext fun u => ?_) ?_
    · change ⁅(Pi.single v X : RP → RM) u, (Pi.single w Y : RP → RM) u⁆ = 0
      by_cases hu : u = v
      · subst hu
        rw [Pi.single_eq_of_ne (Ne.symm h), lie_zero]
      · rw [Pi.single_eq_of_ne hu, zero_lie]
    · exact lie_zero _
  exact (realLiePlaceCoordinates F n).injective (h1.trans (map_zero _).symm)

omit [NumberField F] in
theorem lie_realPlace_complexPlaceLieInclusion (v : RP) (w : CP) (X : RM) (Y : CM) :
    ⁅realPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
  classical
  have h1 : realLiePlaceCoordinates F n
      ⁅realPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
    rw [LieEquiv.map_lie, realLiePlaceCoordinates_realInclusion,
      realLiePlaceCoordinates_complexInclusion]
    exact Prod.ext (by exact lie_zero _) (by exact zero_lie _)
  exact (realLiePlaceCoordinates F n).injective (h1.trans (map_zero _).symm)

omit [NumberField F] in
theorem lie_realPlaceComplexLieInclusion_of_ne {v w : RP} (h : w ≠ v)
    (X Y : ℂ ⊗[ℝ] RM) :
    ⁅realPlaceComplexLieInclusion F n v X, realPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | add X₁ X₂ h₁ h₂ =>
    rw [map_add]
    have h3 := add_lie (realPlaceComplexLieInclusion F n v X₁)
      (realPlaceComplexLieInclusion F n v X₂) (realPlaceComplexLieInclusion F n w Y)
    rw [h₁, h₂, add_zero] at h3
    exact h3
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | add Y₁ Y₂ h₁ h₂ =>
      rw [map_add]
      have h3 := lie_add (realPlaceComplexLieInclusion F n v (z ⊗ₜ[ℝ] X))
        (realPlaceComplexLieInclusion F n w Y₁) (realPlaceComplexLieInclusion F n w Y₂)
      rw [h₁, h₂, add_zero] at h3
      exact h3
    | tmul z' Y =>
      rw [realPlaceComplexLieInclusion_tmul, realPlaceComplexLieInclusion_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, lie_realPlaceLieInclusion_of_ne h,
        TensorProduct.tmul_zero]

omit [NumberField F] in
theorem lie_realPlace_complexPlaceComplexLieInclusion (v : RP) (w : CP)
    (X : ℂ ⊗[ℝ] RM) (Y : ℂ ⊗[ℝ] CM) :
    ⁅realPlaceComplexLieInclusion F n v X, complexPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | add X₁ X₂ h₁ h₂ =>
    rw [map_add]
    have h3 := add_lie (realPlaceComplexLieInclusion F n v X₁)
      (realPlaceComplexLieInclusion F n v X₂) (complexPlaceComplexLieInclusion F n w Y)
    rw [h₁, h₂, add_zero] at h3
    exact h3
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | add Y₁ Y₂ h₁ h₂ =>
      rw [map_add]
      have h3 := lie_add (realPlaceComplexLieInclusion F n v (z ⊗ₜ[ℝ] X))
        (complexPlaceComplexLieInclusion F n w Y₁) (complexPlaceComplexLieInclusion F n w Y₂)
      rw [h₁, h₂, add_zero] at h3
      exact h3
    | tmul z' Y =>
      rw [realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, lie_realPlace_complexPlaceLieInclusion,
        TensorProduct.tmul_zero]

omit [NumberField F] in
theorem lie_complexPlaceLieInclusion_of_ne {v w : CP} (h : w ≠ v) (X Y : CM) :
    ⁅complexPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
  classical
  have h1 : realLiePlaceCoordinates F n
      ⁅complexPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
    rw [LieEquiv.map_lie, realLiePlaceCoordinates_complexInclusion,
      realLiePlaceCoordinates_complexInclusion]
    refine Prod.ext ?_ (funext fun u => ?_)
    · exact lie_zero _
    · change ⁅(Pi.single v X : CP → CM) u, (Pi.single w Y : CP → CM) u⁆ = 0
      by_cases hu : u = v
      · subst hu
        rw [Pi.single_eq_of_ne (Ne.symm h), lie_zero]
      · rw [Pi.single_eq_of_ne hu, zero_lie]
  exact (realLiePlaceCoordinates F n).injective (h1.trans (map_zero _).symm)

omit [NumberField F] in
theorem lie_complexPlaceComplexLieInclusion_of_ne {v w : CP} (h : w ≠ v)
    (X Y : ℂ ⊗[ℝ] CM) :
    ⁅complexPlaceComplexLieInclusion F n v X, complexPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | add X₁ X₂ h₁ h₂ =>
    rw [map_add]
    have h3 := add_lie (complexPlaceComplexLieInclusion F n v X₁)
      (complexPlaceComplexLieInclusion F n v X₂) (complexPlaceComplexLieInclusion F n w Y)
    rw [h₁, h₂, add_zero] at h3
    exact h3
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | add Y₁ Y₂ h₁ h₂ =>
      rw [map_add]
      have h3 := lie_add (complexPlaceComplexLieInclusion F n v (z ⊗ₜ[ℝ] X))
        (complexPlaceComplexLieInclusion F n w Y₁) (complexPlaceComplexLieInclusion F n w Y₂)
      rw [h₁, h₂, add_zero] at h3
      exact h3
    | tmul z' Y =>
      rw [complexPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, lie_complexPlaceLieInclusion_of_ne h,
        TensorProduct.tmul_zero]

theorem unitaryMatrixComplexLieConjugation_one' (𝕜 : Type*) [RCLike 𝕜]
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) :
    unitaryMatrixComplexLieConjugation 𝕜 n 1 X = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simp only [map_add, hX, hY]

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-! ### The place actions at a real place -/

theorem isLocallyFinite_realPlace (v : RP) :
    IsLocallyFinite (S.realPlaceCompactRepresentation v) := fun x =>
  ⟨FiniteVectors.orbitSpan _ x, S.realPlaceCompactRepresentation_isFiniteVector v x,
    FiniteVectors.self_mem_orbitSpan _ x,
    fun k _ hy => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule k hy⟩

theorem isWeaklyContinuous_realPlace (v : RP) :
    IsWeaklyContinuous (S.realPlaceCompactRepresentation v) :=
  fun μ x => S.continuous_dual_realPlaceCompactRepresentation v μ x

/-- Lie actions at distinct real places commute. -/
theorem realPlaceLieAction_comm_of_ne {v w : RP} (h : w ≠ v) (X Y : ℂ ⊗[ℝ] RM)
    (f : S.Space) :
    S.realPlaceLieAction v X (S.realPlaceLieAction w Y f) =
      S.realPlaceLieAction w Y (S.realPlaceLieAction v X f) := by
  have h0 := congrArg (fun A : Module.End ℂ S.Space => A f)
    (S.complexLieAction.map_lie (realPlaceComplexLieInclusion F n v X)
      (realPlaceComplexLieInclusion F n w Y))
  simp only [lie_realPlaceComplexLieInclusion_of_ne h, map_zero, LinearMap.zero_apply,
    Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h0
  exact (sub_eq_zero.mp h0.symm)

/-- The Lie action at a real place commutes with the Lie actions at complex places. -/
theorem realPlaceLieAction_comm_complexPlace (v : RP) (w : CP) (X : ℂ ⊗[ℝ] RM)
    (Y : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.realPlaceLieAction v X (S.complexPlaceLieAction w Y f) =
      S.complexPlaceLieAction w Y (S.realPlaceLieAction v X f) := by
  have h0 := congrArg (fun A : Module.End ℂ S.Space => A f)
    (S.complexLieAction.map_lie (realPlaceComplexLieInclusion F n v X)
      (complexPlaceComplexLieInclusion F n w Y))
  simp only [lie_realPlace_complexPlaceComplexLieInclusion, map_zero, LinearMap.zero_apply,
    Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h0
  exact (sub_eq_zero.mp h0.symm)

/-! ### The place actions at a complex place -/

theorem isLocallyFinite_complexPlace (v : CP) :
    IsLocallyFinite (S.complexPlaceCompactRepresentation v) := fun x =>
  ⟨FiniteVectors.orbitSpan _ x, S.complexPlaceCompactRepresentation_isFiniteVector v x,
    FiniteVectors.self_mem_orbitSpan _ x,
    fun k _ hy => (FiniteVectors.orbitSubrepresentation _ x).apply_mem_toSubmodule k hy⟩

theorem isWeaklyContinuous_complexPlace (v : CP) :
    IsWeaklyContinuous (S.complexPlaceCompactRepresentation v) :=
  fun μ x => S.continuous_dual_complexPlaceCompactRepresentation v μ x

/-- Lie actions at distinct complex places commute. -/
theorem complexPlaceLieAction_comm_of_ne {v w : CP} (h : w ≠ v) (X Y : ℂ ⊗[ℝ] CM)
    (f : S.Space) :
    S.complexPlaceLieAction v X (S.complexPlaceLieAction w Y f) =
      S.complexPlaceLieAction w Y (S.complexPlaceLieAction v X f) := by
  have h0 := congrArg (fun A : Module.End ℂ S.Space => A f)
    (S.complexLieAction.map_lie (complexPlaceComplexLieInclusion F n v X)
      (complexPlaceComplexLieInclusion F n w Y))
  simp only [lie_complexPlaceComplexLieInclusion_of_ne h, map_zero, LinearMap.zero_apply,
    Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h0
  exact (sub_eq_zero.mp h0.symm)

/-! ### The free set at a real place -/

section RealFreeSet

/-- The vectors whose stable hull for the place actions at `v` has no nonzero
`τ`-intertwiner. -/
abbrev realFreeSet (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ S.Space :=
  freeSet (S.realPlaceLieAction v) (S.isLocallyFinite_realPlace v)
    (S.isWeaklyContinuous_realPlace v) τ

theorem realFreeSet_finite (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (g : FiniteAdelicGL F n) {x : S.Space}
    (hx : x ∈ S.realFreeSet v τ) : S.finiteRepresentation g x ∈ S.realFreeSet v τ :=
  freeSet_map (S.finiteRepresentation g)
    (fun k y => S.finiteRepresentation_realPlaceCompactRepresentation g v k y)
    (fun X y => S.finiteRepresentation_realPlaceLieAction g v X y) hx

theorem realFreeSet_realLie (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    {w : RP} (X : ℂ ⊗[ℝ] RM) {x : S.Space}
    (hx : x ∈ S.realFreeSet v τ) : S.realPlaceLieAction w X x ∈ S.realFreeSet v τ := by
  by_cases hw : w = v
  · subst hw
    exact freeSet_lie X hx
  · exact freeSet_map (S.realPlaceLieAction w X)
      (fun k y => (S.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w hw k X y).symm)
      (fun Y y => (S.realPlaceLieAction_comm_of_ne hw Y X y).symm) hx

theorem realFreeSet_complexLie (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (w : CP) (X : ℂ ⊗[ℝ] CM) {x : S.Space}
    (hx : x ∈ S.realFreeSet v τ) : S.complexPlaceLieAction w X x ∈ S.realFreeSet v τ :=
  freeSet_map (S.complexPlaceLieAction w X)
    (fun k y => (S.realPlaceCompactRepresentation_complexPlaceLieAction v w k X y).symm)
    (fun Y y => (S.realPlaceLieAction_comm_complexPlace v w Y X y).symm) hx

theorem realFreeSet_complexLieAction (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (Y : ComplexLieAlgebra F n) {x : S.Space}
    (hx : x ∈ S.realFreeSet v τ) : S.complexLieAction Y x ∈ S.realFreeSet v τ := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexLieAction (z ⊗ₜ[ℝ] X) x =
        z • S.complexLieAction (complexify F n X) x :=
      (congrArg (fun Y => S.complexLieAction Y x) hzX).trans
        (LinearMap.congr_fun (S.complexLieAction.map_smul z (complexify F n X)) x)
    have hmem : S.complexLieAction (complexify F n X) x ∈ S.realFreeSet v τ := by
      refine (congrArg (fun y => y ∈ S.realFreeSet v τ)
        (S.complexify_action_eq_sum_place X x)).mpr ?_
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun w _ => ?_)
        (Submodule.sum_mem _ fun w _ => ?_)
      · exact S.realFreeSet_realLie v τ _ hx
      · exact S.realFreeSet_complexLie v τ w _ hx
    exact (congrArg (fun y => y ∈ S.realFreeSet v τ) heq).mpr (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : S.complexLieAction (Y₁ + Y₂) x =
        S.complexLieAction Y₁ x + S.complexLieAction Y₂ x :=
      LinearMap.congr_fun (S.complexLieAction.map_add Y₁ Y₂) x
    exact (congrArg (fun y => y ∈ S.realFreeSet v τ) heq).mpr (Submodule.add_mem _ h₁ h₂)

theorem realFreeSet_enveloping (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (u : EnvelopingAlgebra F n) :
    ∀ x ∈ S.realFreeSet v τ, S.envelopingAction u x ∈ S.realFreeSet v τ := by
  have hu : u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F n → EnvelopingAlgebra F n)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨Y, rfl⟩ := hu
    intro x hx
    exact S.realFreeSet_complexLieAction v τ Y hx
  | algebraMap c =>
    intro x hx
    have heq : S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n) c) x = c • x :=
      LinearMap.congr_fun (S.envelopingAction.commutes c) x
    exact (congrArg (fun y => y ∈ S.realFreeSet v τ) heq).mpr (Submodule.smul_mem _ c hx)
  | add a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a + b) x = S.envelopingAction a x + S.envelopingAction b x :=
      LinearMap.congr_fun (S.envelopingAction.map_add a b) x
    exact (congrArg (fun y => y ∈ S.realFreeSet v τ) heq).mpr
      (Submodule.add_mem _ (ha x hx) (hb x hx))
  | mul a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a * b) x = S.envelopingAction a (S.envelopingAction b x) :=
      LinearMap.congr_fun (S.envelopingAction.map_mul a b) x
    exact (congrArg (fun y => y ∈ S.realFreeSet v τ) heq).mpr (ha _ (hb x hx))

theorem realFreeSet_compact (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (k : standardInfiniteCompact F n) {x : S.Space}
    (hx : x ∈ S.realFreeSet v τ) : S.compactRepresentation k x ∈ S.realFreeSet v τ := by
  classical
  refine (ArchimedeanCompactFactors.toStandardCompact_surjective F n k).elim fun p hpk => ?_
  have hex : ∃ p' : ArchimedeanCompactFactors F n,
      p'.1 = Function.update p.1 v 1 ∧ p'.2 = p.2 := ⟨(Function.update p.1 v 1, p.2), rfl, rfl⟩
  refine hex.elim fun p' hp' => ?_
  have hp'1 := hp'.1
  have hp'2 := hp'.2
  have hp : p = ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * p' := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p.1 w = (Pi.mulSingle v (p.1 v) : RP → RK) w * p'.1 w
      rw [hp'1]
      by_cases hw : w = v
      · subst hw
        rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw, one_mul]
    · change p.2 w = 1 * p'.2 w
      rw [hp'2, one_mul]
  have hcomm : ∀ l : RK, p' * ArchimedeanCompactFactors.realPlaceFactor F n v l =
      ArchimedeanCompactFactors.realPlaceFactor F n v l * p' := fun l => by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p'.1 w * (Pi.mulSingle v l : RP → RK) w = (Pi.mulSingle v l : RP → RK) w * p'.1 w
      rw [hp'1]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, one_mul, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
    · change p'.2 w * 1 = 1 * p'.2 w
      rw [mul_one, one_mul]
  have hCκ : ∀ (l : RK) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.realPlaceCompactRepresentation v l y) =
        S.realPlaceCompactRepresentation v l
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro l y
    have hk : ArchimedeanCompactFactors.toStandardCompact F n p' *
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l) =
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l) *
        ArchimedeanCompactFactors.toStandardCompact F n p' := by
      rw [← map_mul, ← map_mul, hcomm l]
    have h1 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l)) =
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l)) *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
      (S.compactRepresentation.map_mul _ _).symm.trans
        ((congrArg S.compactRepresentation hk).trans (S.compactRepresentation.map_mul _ _))
    exact LinearMap.congr_fun h1 y
  have hp'v : p'.1 v = 1 := by rw [hp'1, Function.update_self]
  have hCπ : ∀ (X : ℂ ⊗[ℝ] RM) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.realPlaceLieAction v X y) =
        S.realPlaceLieAction v X
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro X y
    have hX : unitaryMatrixComplexLieConjugation ℝ n (p'.1 v) X = X := by
      rw [hp'v, unitaryMatrixComplexLieConjugation_one' ℝ X]
    exact (S.compactRepresentation_realPlaceLieAction p' v X y).trans
      (congrArg (fun Z => S.realPlaceLieAction v Z
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y)) hX)
  have hCx : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x ∈
      S.realFreeSet v τ := freeSet_map _ hCκ hCπ hx
  have h2 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * p')) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v))) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
    (congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)
  have hsplit : S.compactRepresentation k x =
      S.realPlaceCompactRepresentation v (p.1 v)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x) :=
    ((congrArg (fun r => S.compactRepresentation r x) hpk.symm).trans
      (congrArg (fun r => S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n r) x) hp)).trans
      (LinearMap.congr_fun h2 x)
  exact (congrArg (fun y => y ∈ S.realFreeSet v τ) hsplit).mpr (freeSet_compact (p.1 v) hCx)

/-- The free set is preserved by the whole concrete operator algebra. -/
theorem realFreeSet_operator (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (a : automorphicOperatorAlgebra F n) :
    ∀ x ∈ S.realFreeSet v τ, S.representation a x ∈ S.realFreeSet v τ := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact fun x hx => S.realFreeSet_finite v τ g hx
    · exact fun x hx => S.realFreeSet_compact v τ k hx
    · exact fun x hx => S.realFreeSet_enveloping v τ u x hx
  | algebraMap c =>
    intro x hx
    have h : S.representation ⟨algebraMap ℂ (FiniteSmoothEnd F n) c,
        Subalgebra.algebraMap_mem _ c⟩ x = c • x := rfl
    rw [h]
    exact Submodule.smul_mem _ c hx
  | add e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ + e₂, Subalgebra.add_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ x + S.representation ⟨e₂, he₂⟩ x := rfl
    rw [h]
    exact Submodule.add_mem _ (h₁ x hx) (h₂ x hx)
  | mul e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ * e₂, Subalgebra.mul_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ (S.representation ⟨e₂, he₂⟩ x) := rfl
    rw [h]
    exact h₁ _ (h₂ x hx)

/-- In an irreducible realization the free set is zero as soon as one vector is not free. -/
theorem realFreeSet_eq_bot (v : RP) {d : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (hS : S.IsIrreducible) {x₀ : S.Space}
    (hx₀ : x₀ ∉ S.realFreeSet v τ) : S.realFreeSet v τ = ⊥ := by
  let Z : Subrepresentation S.representation :=
    ⟨S.realFreeSet v τ, fun a x hx => S.realFreeSet_operator v τ a x hx⟩
  have hirr : IsSimpleOrder (Subrepresentation S.representation) := hS
  rcases hirr.eq_bot_or_eq_top Z with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · exfalso
    apply hx₀
    have h' : S.realFreeSet v τ = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [h']
    trivial

end RealFreeSet

/-- **Detection at a real place.** A nonzero irreducible operator realization has a
continuous matrix representation of `O(n)` that has a nonzero intertwiner into every nonzero
stable subspace for the place actions at a real place `v`. -/
theorem exists_realPlace_detection (hS : S.IsIrreducible) [Nontrivial S.Space] (v : RP) :
    ∃ (d : ℕ) (τ : RK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W : Submodule ℂ S.Space, IsStable (S.realPlaceCompactRepresentation v)
          (S.realPlaceLieAction v) W → W ≠ ⊥ →
        intertwiners (S.realPlaceCompactRepresentation v) W d τ ≠ ⊥ := by
  refine (exists_ne (0 : S.Space)).elim fun x₀ hx₀ => ?_
  refine (exists_not_mem_freeSet (π := S.realPlaceLieAction v)
    (S.isLocallyFinite_realPlace v) (S.isWeaklyContinuous_realPlace v) hx₀).elim
    fun d hd => hd.elim fun τ hτn => ?_
  have hτ := hτn.1
  have hnot := hτn.2
  have hbot : S.realFreeSet v τ = ⊥ := S.realFreeSet_eq_bot v τ hS hnot
  refine ⟨d, τ, hτ, ?_⟩
  intro W hWs hW
  exact intertwiners_ne_bot_of_freeSet_eq_bot (hfin := S.isLocallyFinite_realPlace v)
    (hweak := S.isWeaklyContinuous_realPlace v) hbot hWs hW

/-! ### The free set at a complex place -/

section ComplexFreeSet

/-- The vectors whose stable hull for the place actions at `v` has no nonzero
`τ`-intertwiner. -/
abbrev complexFreeSet (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ S.Space :=
  freeSet (S.complexPlaceLieAction v) (S.isLocallyFinite_complexPlace v)
    (S.isWeaklyContinuous_complexPlace v) τ

theorem complexFreeSet_finite (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (g : FiniteAdelicGL F n) {x : S.Space}
    (hx : x ∈ S.complexFreeSet v τ) : S.finiteRepresentation g x ∈ S.complexFreeSet v τ :=
  freeSet_map (S.finiteRepresentation g)
    (fun k y => S.finiteRepresentation_complexPlaceCompactRepresentation g v k y)
    (fun X y => S.finiteRepresentation_complexPlaceLieAction g v X y) hx

theorem complexFreeSet_realLie (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (w : RP) (X : ℂ ⊗[ℝ] RM) {x : S.Space}
    (hx : x ∈ S.complexFreeSet v τ) : S.realPlaceLieAction w X x ∈ S.complexFreeSet v τ :=
  freeSet_map (S.realPlaceLieAction w X)
    (fun k y => (S.complexPlaceCompactRepresentation_realPlaceLieAction v w k X y).symm)
    (fun Y y => S.realPlaceLieAction_comm_complexPlace w v X Y y) hx

theorem complexFreeSet_complexLie (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    {w : CP} (X : ℂ ⊗[ℝ] CM) {x : S.Space}
    (hx : x ∈ S.complexFreeSet v τ) : S.complexPlaceLieAction w X x ∈ S.complexFreeSet v τ := by
  by_cases hw : w = v
  · subst hw
    exact freeSet_lie X hx
  · exact freeSet_map (S.complexPlaceLieAction w X)
      (fun k y =>
        (S.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne v w hw k X y).symm)
      (fun Y y => (S.complexPlaceLieAction_comm_of_ne hw Y X y).symm) hx

theorem complexFreeSet_complexLieAction (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (Y : ComplexLieAlgebra F n) {x : S.Space}
    (hx : x ∈ S.complexFreeSet v τ) : S.complexLieAction Y x ∈ S.complexFreeSet v τ := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexLieAction (z ⊗ₜ[ℝ] X) x =
        z • S.complexLieAction (complexify F n X) x :=
      (congrArg (fun Y => S.complexLieAction Y x) hzX).trans
        (LinearMap.congr_fun (S.complexLieAction.map_smul z (complexify F n X)) x)
    have hmem : S.complexLieAction (complexify F n X) x ∈ S.complexFreeSet v τ := by
      refine (congrArg (fun y => y ∈ S.complexFreeSet v τ)
        (S.complexify_action_eq_sum_place X x)).mpr ?_
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun w _ => ?_)
        (Submodule.sum_mem _ fun w _ => ?_)
      · exact S.complexFreeSet_realLie v τ w _ hx
      · exact S.complexFreeSet_complexLie v τ _ hx
    exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) heq).mpr (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : S.complexLieAction (Y₁ + Y₂) x =
        S.complexLieAction Y₁ x + S.complexLieAction Y₂ x :=
      LinearMap.congr_fun (S.complexLieAction.map_add Y₁ Y₂) x
    exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) heq).mpr (Submodule.add_mem _ h₁ h₂)

theorem complexFreeSet_enveloping (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (u : EnvelopingAlgebra F n) :
    ∀ x ∈ S.complexFreeSet v τ, S.envelopingAction u x ∈ S.complexFreeSet v τ := by
  have hu : u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F n → EnvelopingAlgebra F n)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨Y, rfl⟩ := hu
    intro x hx
    exact S.complexFreeSet_complexLieAction v τ Y hx
  | algebraMap c =>
    intro x hx
    have heq : S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n) c) x = c • x :=
      LinearMap.congr_fun (S.envelopingAction.commutes c) x
    exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) heq).mpr (Submodule.smul_mem _ c hx)
  | add a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a + b) x = S.envelopingAction a x + S.envelopingAction b x :=
      LinearMap.congr_fun (S.envelopingAction.map_add a b) x
    exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) heq).mpr
      (Submodule.add_mem _ (ha x hx) (hb x hx))
  | mul a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a * b) x = S.envelopingAction a (S.envelopingAction b x) :=
      LinearMap.congr_fun (S.envelopingAction.map_mul a b) x
    exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) heq).mpr (ha _ (hb x hx))

theorem complexFreeSet_compact (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (k : standardInfiniteCompact F n) {x : S.Space}
    (hx : x ∈ S.complexFreeSet v τ) : S.compactRepresentation k x ∈ S.complexFreeSet v τ := by
  classical
  refine (ArchimedeanCompactFactors.toStandardCompact_surjective F n k).elim fun p hpk => ?_
  have hex : ∃ p' : ArchimedeanCompactFactors F n,
      p'.1 = p.1 ∧ p'.2 = Function.update p.2 v 1 := ⟨(p.1, Function.update p.2 v 1), rfl, rfl⟩
  refine hex.elim fun p' hp' => ?_
  have hp'1 := hp'.1
  have hp'2 := hp'.2
  have hp : p = ArchimedeanCompactFactors.complexPlaceFactor F n v (p.2 v) * p' := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p.1 w = 1 * p'.1 w
      rw [hp'1, one_mul]
    · change p.2 w = (Pi.mulSingle v (p.2 v) : CP → CK) w * p'.2 w
      rw [hp'2]
      by_cases hw : w = v
      · subst hw
        rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw, one_mul]
  have hcomm : ∀ l : CK, p' * ArchimedeanCompactFactors.complexPlaceFactor F n v l =
      ArchimedeanCompactFactors.complexPlaceFactor F n v l * p' := fun l => by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p'.1 w * 1 = 1 * p'.1 w
      rw [mul_one, one_mul]
    · change p'.2 w * (Pi.mulSingle v l : CP → CK) w = (Pi.mulSingle v l : CP → CK) w * p'.2 w
      rw [hp'2]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, one_mul, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
  have hCκ : ∀ (l : CK) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.complexPlaceCompactRepresentation v l y) =
        S.complexPlaceCompactRepresentation v l
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro l y
    have hk : ArchimedeanCompactFactors.toStandardCompact F n p' *
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.complexPlaceFactor F n v l) =
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.complexPlaceFactor F n v l) *
        ArchimedeanCompactFactors.toStandardCompact F n p' := by
      rw [← map_mul, ← map_mul, hcomm l]
    have h1 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.complexPlaceFactor F n v l)) =
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.complexPlaceFactor F n v l)) *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
      (S.compactRepresentation.map_mul _ _).symm.trans
        ((congrArg S.compactRepresentation hk).trans (S.compactRepresentation.map_mul _ _))
    exact LinearMap.congr_fun h1 y
  have hp'v : p'.2 v = 1 := by rw [hp'2, Function.update_self]
  have hCπ : ∀ (X : ℂ ⊗[ℝ] CM) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.complexPlaceLieAction v X y) =
        S.complexPlaceLieAction v X
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro X y
    have hX : unitaryMatrixComplexLieConjugation ℂ n (p'.2 v) X = X := by
      rw [hp'v, unitaryMatrixComplexLieConjugation_one' ℂ X]
    exact (S.compactRepresentation_complexPlaceLieAction p' v X y).trans
      (congrArg (fun Z => S.complexPlaceLieAction v Z
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y)) hX)
  have hCx : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x ∈
      S.complexFreeSet v τ := freeSet_map _ hCκ hCπ hx
  have h2 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v (p.2 v) * p')) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v (p.2 v))) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
    (congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)
  have hsplit : S.compactRepresentation k x =
      S.complexPlaceCompactRepresentation v (p.2 v)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x) :=
    ((congrArg (fun r => S.compactRepresentation r x) hpk.symm).trans
      (congrArg (fun r => S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n r) x) hp)).trans
      (LinearMap.congr_fun h2 x)
  exact (congrArg (fun y => y ∈ S.complexFreeSet v τ) hsplit).mpr (freeSet_compact (p.2 v) hCx)

/-- The free set is preserved by the whole concrete operator algebra. -/
theorem complexFreeSet_operator (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (a : automorphicOperatorAlgebra F n) :
    ∀ x ∈ S.complexFreeSet v τ, S.representation a x ∈ S.complexFreeSet v τ := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact fun x hx => S.complexFreeSet_finite v τ g hx
    · exact fun x hx => S.complexFreeSet_compact v τ k hx
    · exact fun x hx => S.complexFreeSet_enveloping v τ u x hx
  | algebraMap c =>
    intro x hx
    have h : S.representation ⟨algebraMap ℂ (FiniteSmoothEnd F n) c,
        Subalgebra.algebraMap_mem _ c⟩ x = c • x := rfl
    rw [h]
    exact Submodule.smul_mem _ c hx
  | add e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ + e₂, Subalgebra.add_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ x + S.representation ⟨e₂, he₂⟩ x := rfl
    rw [h]
    exact Submodule.add_mem _ (h₁ x hx) (h₂ x hx)
  | mul e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ * e₂, Subalgebra.mul_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ (S.representation ⟨e₂, he₂⟩ x) := rfl
    rw [h]
    exact h₁ _ (h₂ x hx)

/-- In an irreducible realization the free set is zero as soon as one vector is not free. -/
theorem complexFreeSet_eq_bot (v : CP) {d : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (hS : S.IsIrreducible) {x₀ : S.Space}
    (hx₀ : x₀ ∉ S.complexFreeSet v τ) : S.complexFreeSet v τ = ⊥ := by
  let Z : Subrepresentation S.representation :=
    ⟨S.complexFreeSet v τ, fun a x hx => S.complexFreeSet_operator v τ a x hx⟩
  have hirr : IsSimpleOrder (Subrepresentation S.representation) := hS
  rcases hirr.eq_bot_or_eq_top Z with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · exfalso
    apply hx₀
    have h' : S.complexFreeSet v τ = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [h']
    trivial

end ComplexFreeSet

/-- **Detection at a complex place.** A nonzero irreducible operator realization has a
continuous matrix representation of `U(n)` that has a nonzero intertwiner into every nonzero
stable subspace for the place actions at a complex place `v`. -/
theorem exists_complexPlace_detection (hS : S.IsIrreducible) [Nontrivial S.Space] (v : CP) :
    ∃ (d : ℕ) (τ : CK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W : Submodule ℂ S.Space, IsStable (S.complexPlaceCompactRepresentation v)
          (S.complexPlaceLieAction v) W → W ≠ ⊥ →
        intertwiners (S.complexPlaceCompactRepresentation v) W d τ ≠ ⊥ := by
  refine (exists_ne (0 : S.Space)).elim fun x₀ hx₀ => ?_
  refine (exists_not_mem_freeSet (π := S.complexPlaceLieAction v)
    (S.isLocallyFinite_complexPlace v) (S.isWeaklyContinuous_complexPlace v) hx₀).elim
    fun d hd => hd.elim fun τ hτn => ?_
  have hτ := hτn.1
  have hnot := hτn.2
  have hbot : S.complexFreeSet v τ = ⊥ := S.complexFreeSet_eq_bot v τ hS hnot
  refine ⟨d, τ, hτ, ?_⟩
  intro W hWs hW
  exact intertwiners_ne_bot_of_freeSet_eq_bot (hfin := S.isLocallyFinite_complexPlace v)
    (hweak := S.isWeaklyContinuous_complexPlace v) hbot hWs hW

end OperatorRealization

end Langlands.Automorphic
