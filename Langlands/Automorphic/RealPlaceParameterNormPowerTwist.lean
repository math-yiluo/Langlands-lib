import Langlands.Representation.Archimedean.RealStandardComplexTwist
import Langlands.Representation.Category.CentralCharacterRegularity
import Langlands.Automorphic.ComplexPlaceParameterHeckeTwist
import Langlands.Global.RankinSelberg.RealPlaceDeterminantGrowth
import Langlands.Global.HeckeNormPower

/-!
# Real-place parameters under twists by complex powers of the norm

If an actual automorphic realization `S` has the standard-module parameter `ds` at a real place
`v`, then its twist `S.heckeDeterminantTwist (HeckeCharacter.normPower F s)` by
`‖·‖^s ∘ det`, for a complex `s`, has the parameter of the blocks of `ds` with `s` added to
every exponent. See the paired Markdown.
-/

noncomputable section

universe u

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.RealPlaceNormPowerTwist

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean NumberField
open Langlands.Archimedean.RealLinkedJacquetStages (detPow contMDiff_detPow ofReal_abs_det_ne_zero)
open Langlands.Automorphic.ComplexPlaceHeckeTwist (characterExtension characterExtension_unit
  differentiableAt_characterExtension_one)

attribute [local instance 100] LieRing.ofAssociativeRing

local instance realNormPowerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (RankinSelbergGlobal.Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realNormPowerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (RankinSelbergGlobal.Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}

/-! ## The norm power on determinants -/

/-- `‖det g‖^s` is `exp (s log ‖det g‖)` for the actual adelic determinant norm. -/
theorem normPower_adelicDeterminant (n : ℕ) (s : ℂ) (g : AdelicGL F n) :
    ((HeckeCharacter.normPower F s).adelicDeterminant n g : ℂ) =
      Complex.exp (s * (Real.log
        (((AdelicBlockDeterminantCharacter.determinantNorm F n g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ)) := by
  change ((HeckeCharacter.normPower F s) (ideleClassMap F (AdelicGL.determinant F n g)) : ℂ) = _
  rw [HeckeCharacter.normPower_apply, IdeleAbsoluteValue.ideleClass_class]
  rfl

variable (n : ℕ)

/-- The adelic determinant norm of the infinite matrix `ι_v(g)` is `|det g|`. -/
theorem determinantNorm_ofInfinite_realPlaceGL (v : RP) (g : Langlands.GeneralLinear n ℝ) :
    (((AdelicBlockDeterminantCharacter.determinantNorm F n
      (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm
        (RankinSelbergGlobal.realPlaceGL F n v g))) : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      |(g : Matrix (Fin n) (Fin n) ℝ).det| := by
  have h := RankinSelbergGlobal.RealPlaceRestriction.detNorm_realPlacePoint F n v g
  have he : GeneralLinearGroupPoints.adelicEquiv F n
      (RankinSelbergGlobal.realPlacePoint F n v g) =
        AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm
          (RankinSelbergGlobal.realPlaceGL F n v g)) := by
    simp only [RankinSelbergGlobal.realPlacePoint, RankinSelbergGlobal.adelicPoint,
      MulEquiv.apply_symm_apply, AdelicGL.pair_eq_ofInfinite_mul_ofFinite, map_one, mul_one]
  rw [← he]
  exact h

/-- The value of `‖·‖^s ∘ det` at the infinite matrix `ι_v(g)` is `|det g|^s`. -/
theorem normPower_adelicDeterminant_realPlaceGL (s : ℂ) (v : RP)
    (g : Langlands.GeneralLinear n ℝ) :
    ((HeckeCharacter.normPower F s).adelicDeterminant n
      (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm
        (RankinSelbergGlobal.realPlaceGL F n v g))) : ℂ) = detPow n s g := by
  rw [normPower_adelicDeterminant, determinantNorm_ofInfinite_realPlaceGL, detPow,
    Complex.cpow_def_of_ne_zero (ofReal_abs_det_ne_zero g),
    ← Complex.ofReal_log (abs_nonneg _), mul_comm]

/-- `‖·‖^s ∘ det` is trivial on the standard infinite compact subgroup. -/
theorem normPower_adelicDeterminant_compact (s : ℂ) (k : standardInfiniteCompact F n) :
    (HeckeCharacter.normPower F s).adelicDeterminant n (AdelicGL.ofInfinite F n k.val) = 1 := by
  set N : ℝ := (((AdelicBlockDeterminantCharacter.determinantNorm F n
    (AdelicGL.ofInfinite F n k.val) : ℝ≥0ˣ) : ℝ≥0) : ℝ) with hN
  have hpos : 0 < N := by
    have h := (AdelicBlockDeterminantCharacter.determinantNorm F n
      (AdelicGL.ofInfinite F n k.val)).ne_zero
    rw [hN]
    positivity
  let f : standardInfiniteCompact F n →* ℂˣ :=
    ((HeckeCharacter.normPower F 1).adelicDeterminant n).toMonoidHom.comp
      ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)
  have hf : Continuous f := ((HeckeCharacter.normPower F 1).adelicDeterminant n).continuous.comp
    ((AdelicGL.ofInfinite F n).continuous.comp continuous_subtype_val)
  have hk := Langlands.norm_eq_one_of_compact_quotient f hf ⊥ (by
    intro z hz
    rw [Subgroup.mem_bot.mp hz, map_one, Units.val_one, norm_one]) k
  have hfk : ((f k : ℂˣ) : ℂ) = (N : ℂ) := by
    change ((HeckeCharacter.normPower F 1).adelicDeterminant n
      (AdelicGL.ofInfinite F n k.val) : ℂ) = _
    rw [normPower_adelicDeterminant, one_mul, ← hN, ← Complex.ofReal_exp, Real.exp_log hpos]
  rw [hfk, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hk
  apply Units.ext
  rw [normPower_adelicDeterminant, ← hN, hk, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, Units.val_one]

/-! ## The real place inside the mixed coordinates -/

section Mixed

open scoped Classical

/-- The archimedean matrix equal to `Y` at the real place `v` and to the identity at every
other place. -/
def realPlaceMatrix (v : RP) (Y : Matrix (Fin n) (Fin n) ℝ) : ArchimedeanMatrix F n :=
  fun i j => (Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j) v (Y i j),
    fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j)

omit [NumberField F] in
/-- The matrix of `ι_v(g)` in mixed coordinates is `realPlaceMatrix v g`. -/
theorem coe_realPlaceGL (v : RP) (g : Langlands.GeneralLinear n ℝ) :
    ((RankinSelbergGlobal.realPlaceGL F n v g : ArchimedeanGL F n) : ArchimedeanMatrix F n) =
      realPlaceMatrix n v (g : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  funext i j
  apply Prod.ext
  · funext w
    change ((Pi.mulSingle v g : RP → Langlands.GeneralLinear n ℝ) w :
      Matrix (Fin n) (Fin n) ℝ) i j = _
    by_cases hw : w = v
    · subst hw
      simp [realPlaceMatrix]
    · simp [realPlaceMatrix, Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw]
  · funext w
    rfl

omit [NumberField F] in
/-- The identity at `v` gives the identity matrix. -/
theorem realPlaceMatrix_one (v : RP) : realPlaceMatrix n v (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h := coe_realPlaceGL (F := F) n v 1
  rw [map_one, Units.val_one, Units.val_one] at h
  exact h.symm

/-- The linear part of `realPlaceMatrix v`: the matrix `Y` at `v` and zero elsewhere. -/
def realPlaceLinear (v : RP) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ArchimedeanMatrix F n where
  toFun Y i j := (Pi.single v (Y i j), 0)
  map_add' Y Z := by
    funext i j
    apply Prod.ext
    · funext w
      by_cases hw : w = v <;> simp [hw]
    · simp
  map_smul' r Y := by
    funext i j
    apply Prod.ext
    · funext w
      by_cases hw : w = v <;> simp [hw]
    · simp

omit [NumberField F] in
/-- `realPlaceMatrix v` is affine with linear part `realPlaceLinear v`. -/
theorem realPlaceMatrix_eq (v : RP) (Y : Matrix (Fin n) (Fin n) ℝ) :
    realPlaceMatrix n v Y = realPlaceMatrix n v 0 + realPlaceLinear n v Y := by
  classical
  funext i j
  apply Prod.ext
  · funext w
    by_cases hw : w = v
    · subst hw
      simp [realPlaceMatrix, realPlaceLinear]
    · simp [realPlaceMatrix, realPlaceLinear, hw]
  · funext w
    simp [realPlaceMatrix, realPlaceLinear]

/-- The continuous linear part of `realPlaceMatrix v`. -/
def realPlaceLinearCLM (v : RP) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ArchimedeanMatrix F n :=
  LinearMap.toContinuousLinearMap (realPlaceLinear n v)

/-- The derivative of `realPlaceMatrix v` is its linear part. -/
theorem hasFDerivAt_realPlaceMatrix (v : RP) (Y : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (realPlaceMatrix (F := F) n v) (realPlaceLinearCLM n v) Y := by
  have h : HasFDerivAt
      (fun Z => realPlaceMatrix (F := F) n v 0 + realPlaceLinearCLM (F := F) n v Z)
      (realPlaceLinearCLM (F := F) n v) Y :=
    (realPlaceLinearCLM (F := F) n v).hasFDerivAt.const_add (realPlaceMatrix (F := F) n v 0)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
  exact realPlaceMatrix_eq n v Z

omit [NumberField F] in
/-- The linear part of `realPlaceMatrix v` is the inclusion of the Lie algebra at `v`. -/
theorem realPlaceLinear_eq (v : RP) (X : Matrix (Fin n) (Fin n) ℝ) :
    realPlaceLinear n v X = realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X) := by
  have hc := realLiePlaceCoordinates_realInclusion F n v X
  funext i j
  apply Prod.ext
  · funext w
    have h := congrArg (fun p => p.1 w i j) hc
    refine Eq.trans ?_ h.symm
    change (Pi.single v (X i j) : RP → ℝ) w =
      (Pi.single v X : RP → Matrix (Fin n) (Fin n) ℝ) w i j
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Pi.single_eq_of_ne hw]
  · funext w
    have h := congrArg (fun p => p.2 w i j) hc
    exact h.symm

/-- Near the identity, the archimedean determinant character of `‖·‖^s`, restricted to the
real place `v`, is `|det|^s` on `GL_n(ℝ)`. -/
theorem characterExtension_realPlaceMatrix_eventuallyEq (s : ℂ) (v : RP) :
    (fun Y => characterExtension n (HeckeCharacter.normPower F s) (realPlaceMatrix n v Y)) =ᶠ[𝓝 1]
      unitsExtension (detPow n s) := by
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one (M := Matrix (Fin n) (Fin n) ℝ))]
    with Y hY
  obtain ⟨g, rfl⟩ := hY
  rw [← coe_realPlaceGL, characterExtension_unit, HeckeCharacter.infiniteDeterminantCharacter_apply,
    normPower_adelicDeterminant_realPlaceGL, unitsExtension_val]

/-- The derivative at `1` of the archimedean determinant character of `‖·‖^s` along a direction
at the real place `v` is the derivative at `1` of `|det|^s` on `GL_n(ℝ)`. -/
theorem characterDifferential_realPlaceLieInclusion (s : ℂ) (v : RP)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    characterDifferential ((HeckeCharacter.normPower F s).infiniteDeterminantCharacter n)
        ((HeckeCharacter.normPower F s).infiniteDeterminantCharacter_mem_smoothFunctions n)
        (realPlaceLieInclusion F n v X) =
      rightDerivative (matrixModel ℝ n) X (detPow n s) 1 := by
  set μ := HeckeCharacter.normPower F s
  have hE : ∀ h : ArchimedeanGL F n, characterExtension n μ (h : ArchimedeanMatrix F n) =
      (characterFunction (μ.infiniteDeterminantCharacter n)
        (μ.infiniteDeterminantCharacter_mem_smoothFunctions n)).val
          ((archimedeanGLCoordinates F n).symm h) := fun h => characterExtension_unit n μ h
  have h1 := smoothDifferential_eq_of_extension F n (realPlaceLieInclusion F n v X)
    (characterFunction (μ.infiniteDeterminantCharacter n)
      (μ.infiniteDeterminantCharacter_mem_smoothFunctions n)) (characterExtension n μ) hE 1
  change (smoothDifferential F n (realPlaceLieInclusion F n v X)
    (characterFunction (μ.infiniteDeterminantCharacter n)
      (μ.infiniteDeterminantCharacter_mem_smoothFunctions n))).val 1 = _
  rw [h1, map_one, Units.val_one, one_mul, ← realPlaceLinear_eq,
    rightDerivative_eq_fderiv (contMDiff_detPow s) X 1, Units.val_one, one_mul,
    ← (characterExtension_realPlaceMatrix_eventuallyEq n s v).fderiv_eq]
  have hd := differentiableAt_characterExtension_one n μ
  rw [← realPlaceMatrix_one (F := F) n v] at hd
  have hchain : HasFDerivAt (fun Y => characterExtension n μ (realPlaceMatrix n v Y))
      ((fderiv ℝ (characterExtension n μ) (realPlaceMatrix n v 1)).comp
        (realPlaceLinearCLM n v)) 1 :=
    hd.hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) ℝ) (hasFDerivAt_realPlaceMatrix n v 1)
  rw [hchain.fderiv, realPlaceMatrix_one]
  rfl

end Mixed

end Langlands.Automorphic.RealPlaceNormPowerTwist

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean NumberField
open Langlands.Archimedean.RealComplexTwist
open Langlands.Archimedean.RealLinkedJacquetStages (detPow)
open Langlands.Automorphic.RealPlaceNormPowerTwist

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance realNormPowerTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance realNormPowerTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance realNormPowerTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance realNormPowerTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance realNormPowerTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance realNormPowerTwistSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The twist by `‖·‖^s ∘ det` intertwines the compact actions at a real place. -/
theorem heckeDeterminantTwist_normPower_realPlaceCompact (S : OperatorRealization F n) (s : ℂ)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (k : Matrix.unitaryGroup (Fin n) ℝ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)
        (S.realPlaceCompactRepresentation v k x) =
      (S.heckeDeterminantTwist (HeckeCharacter.normPower F s)).realPlaceCompactRepresentation v k
        (S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s) x) := by
  have hcomp := S.heckeDeterminantTwistEquiv_compact (HeckeCharacter.normPower F s)
    (realPlaceCompactInclusion F n v k) x
  have hc1 : (((HeckeCharacter.normPower F s).adelicDeterminant n
      (AdelicGL.ofInfinite F n (realPlaceCompactInclusion F n v k).val) : ℂˣ) : ℂ) = 1 :=
    (congrArg Units.val (normPower_adelicDeterminant_compact n s
      (realPlaceCompactInclusion F n v k))).trans Units.val_one
  refine (hcomp.trans ?_).symm
  exact (congrArg (· • S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)
    (S.compactRepresentation (realPlaceCompactInclusion F n v k) x)) hc1).trans (one_smul ℂ _)

/-- The twist by `‖·‖^s ∘ det` changes the Lie action of `1 ⊗ X` at a real place by the
derivative of `|det|^s` at the identity along `X`. -/
theorem heckeDeterminantTwist_normPower_realPlaceLie (S : OperatorRealization F n) (s : ℂ)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (X : Matrix (Fin n) (Fin n) ℝ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)
        (S.realPlaceLieAction v (1 ⊗ₜ X) x +
          rightDerivative (matrixModel ℝ n) X (detPow n s) (1 : Langlands.GeneralLinear n ℝ) •
            x) =
      (S.heckeDeterminantTwist (HeckeCharacter.normPower F s)).realPlaceLieAction v (1 ⊗ₜ X)
        (S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s) x) := by
  have hshift : heckeEnvelopingShift n (HeckeCharacter.normPower F s)
      (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X))) =
        envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) +
          algebraMap ℂ (EnvelopingAlgebra F n)
            (rightDerivative (matrixModel ℝ n) X (detPow n s)
              (1 : Langlands.GeneralLinear n ℝ)) := by
    rw [heckeEnvelopingShift, characterShift, envelopingShift_generator,
      realPlaceComplexLieInclusion_tmul, complexCharacterDifferential_tmul, one_mul,
      characterDifferential_realPlaceLieInclusion n s v X]
  have h2 : S.envelopingAction (heckeEnvelopingShift n (HeckeCharacter.normPower F s)
      (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))) x =
      S.realPlaceLieAction v (1 ⊗ₜ X) x +
        rightDerivative (matrixModel ℝ n) X (detPow n s) (1 : Langlands.GeneralLinear n ℝ) • x :=
    calc S.envelopingAction (heckeEnvelopingShift n (HeckeCharacter.normPower F s)
          (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))) x
        = S.envelopingAction
            (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) +
              algebraMap ℂ (EnvelopingAlgebra F n)
                (rightDerivative (matrixModel ℝ n) X (detPow n s)
                  (1 : Langlands.GeneralLinear n ℝ))) x :=
          congrArg (fun u => S.envelopingAction u x) hshift
      _ = S.envelopingAction
            (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X))) x +
          S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n)
            (rightDerivative (matrixModel ℝ n) X (detPow n s)
              (1 : Langlands.GeneralLinear n ℝ))) x :=
          LinearMap.congr_fun (map_add S.envelopingAction _ _) _
      _ = _ :=
          congrArg (S.realPlaceLieAction v (1 ⊗ₜ X) x + ·)
            ((LinearMap.congr_fun (S.envelopingAction.commutes _) _).trans
              (Module.algebraMap_end_apply ℂ ℂ S.Space _ _))
  have hdiff := S.heckeDeterminantTwistEquiv_differential (HeckeCharacter.normPower F s)
    (envelopingGenerator F n (realPlaceComplexLieInclusion F n v (1 ⊗ₜ X))) x
  exact (congrArg (S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)) h2.symm).trans
    (hdiff.symm.trans (OperatorRealization.realPlaceLieAction_apply
      (S.heckeDeterminantTwist (HeckeCharacter.normPower F s)) v (1 ⊗ₜ X)
        (S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s) x)).symm)

set_option maxHeartbeats 800000 in
/-- **Twist rule at a real place.** If `S` has the standard-module parameter `ds` at the real
place `v`, then the twist of `S` by `‖·‖^s ∘ det` has the parameter of the blocks of `ds` with
`s` added to every exponent. -/
theorem HasRealPlaceParameter.heckeDeterminantTwist_normPower {S : OperatorRealization F n}
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}}
    {ds : List RealBlock} (h : S.HasRealPlaceParameter v ds) (s : ℂ) :
    (S.heckeDeterminantTwist (HeckeCharacter.normPower F s)).HasRealPlaceParameter v
      (ds.map (realBlockComplexTwist s)) := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  let N := (RealComplexTwist.twistEquiv s ds hr).symm
  let E := S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)
  refine ⟨(realRank_map_realBlockComplexTwist s ds).trans hr,
    E.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ N.toLinearMap, ?_, ?_, ?_⟩
  · exact E.injective.comp (hA.comp N.injective)
  · intro k f
    have hmemk := rightTranslation_mem_kFiniteFunctions_realStandardModule n
      (ds.map (realBlockComplexTwist s)) f.2 k.2
    refine ⟨hmemk, ?_⟩
    obtain ⟨hmem, hKeq⟩ := hK k (N f)
    have h1 : N ⟨_, hmemk⟩ = ⟨_, hmem⟩ :=
      RealComplexTwist.twistEquiv_symm_rightTranslation s ds hr k.2 f hmemk hmem
    have h2 : E (A (N ⟨_, hmemk⟩)) = E (S.realPlaceCompactRepresentation v
        ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A (N f))) :=
      (congrArg (fun y => E (A y)) h1).trans (congrArg E hKeq)
    exact h2.trans (heckeDeterminantTwist_normPower_realPlaceCompact S s v _ _)
  · intro X f
    have hmemX := rightDerivative_mem_kFiniteFunctions_realStandardModule n
      (ds.map (realBlockComplexTwist s)) f.2 X
    refine ⟨hmemX, ?_⟩
    obtain ⟨hmem, hLeq⟩ := hL X (N f)
    have h1 : A (N ⟨_, hmemX⟩) = S.realPlaceLieAction v (1 ⊗ₜ X) (A (N f)) +
        rightDerivative (matrixModel ℝ n) X (detPow n s) (1 : Langlands.GeneralLinear n ℝ) •
          A (N f) :=
      (congrArg A (RealComplexTwist.twistEquiv_symm_rightDerivative s ds hr X f hmemX hmem)).trans
        ((map_add A _ _).trans (congrArg₂ (· + ·) hLeq (map_smul A _ _)))
    exact (congrArg E h1).trans (heckeDeterminantTwist_normPower_realPlaceLie S s v X _)

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The real-place twist rule for an actual cuspidal realization. -/
theorem hasRealPlaceParameter_heckeDeterminantTwist_normPower
    (S : CuspidalOperatorRealization F r)
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}}
    {ds : List RealBlock} (h : S.realization.HasRealPlaceParameter v ds) (s : ℂ) :
    (S.heckeDeterminantTwist (HeckeCharacter.normPower F s)).realization.HasRealPlaceParameter v
      (ds.map (realBlockComplexTwist s)) :=
  OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist_normPower h s

end CuspidalOperatorRealization

end Langlands.Automorphic
