import Langlands.Global.AdelicBlockHalfModulusTwistPlace
import Langlands.Global.AdelicBlockParabolicPlaceDifferential
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.HeckeTwist.ContragredientTwist
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # The Lie shift of an inverse half-modulus block twist -/

noncomputable section

open scoped BigOperators TensorProduct Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear

variable {R : Type*} [RCLike R] {d : ℕ}

/-- The identity-based curve of invertible matrices \(\exp(tX)\). -/
def matrixExponentialCurve (X : Matrix (Fin d) (Fin d) R) (t : ℝ) :
    Langlands.GeneralLinear d R where
  val := NormedSpace.exp (t • X)
  inv := NormedSpace.exp (-(t • X))
  val_inv := by
    simpa using! (NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_right).symm
  inv_val := by
    simpa using! (NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_left).symm

@[simp]
theorem matrixExponentialCurve_zero (X : Matrix (Fin d) (Fin d) R) :
    matrixExponentialCurve X 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • X) = 1
  simp

theorem hasDerivAt_matrixExponentialCurve_entry (X : Matrix (Fin d) (Fin d) R) (a b : Fin d) :
    HasDerivAt (fun t => (matrixExponentialCurve X t).val a b) (X a b) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
    simpa using! (hasDerivAt_exp_smul_const X (0 : ℝ))
  exact (Matrix.entryLinearMap ℝ R a b).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 h

end Langlands.GeneralLinear

namespace Langlands.Global.FiniteParametrizedBlockInduction

open Langlands.GeneralLinear Langlands.Automorphic Langlands.Archimedean
open AdelicBlockDeterminantCharacter AdelicBlockParabolic ArchimedeanGL RankinSelbergGlobal

universe u

variable {n : ℕ} (B : BlockShape n)

private def blockDirection {R : Type*} [Zero R] (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.reindex B.indexEquiv B.indexEquiv
    (Matrix.blockDiagonal' (Pi.single (M := fun j => Matrix (Fin (B.size j)) (Fin (B.size j)) R) i X))

private theorem blockDirection_apply_same {R : Type*} [Zero R] (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R)
    (j : Fin B.length) (a b : Fin (B.size j)) :
    blockDirection B i X (B.index j a) (B.index j b) =
      (Pi.single (M := fun j => Matrix (Fin (B.size j)) (Fin (B.size j)) R) i X j) a b := by
  simp only [blockDirection, Matrix.reindex_apply, Matrix.submatrix_apply, BlockShape.index,
    Function.Embedding.coeFn_mk, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]

private theorem blockDirection_apply_ne {R : Type*} [Zero R] (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R)
    {j k : Fin B.length} (h : j ≠ k) (a : Fin (B.size j)) (b : Fin (B.size k)) :
    blockDirection B i X (B.index j a) (B.index k b) = 0 := by
  simp only [blockDirection, Matrix.reindex_apply, Matrix.submatrix_apply, BlockShape.index,
    Function.Embedding.coeFn_mk, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h]

private theorem blockTrace_blockDirection {R : Type*} [AddCommMonoid R] (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R) (j : Fin B.length) :
    blockTrace B (blockDirection B i X) j =
      (Pi.single (M := fun j => Matrix (Fin (B.size j)) (Fin (B.size j)) R) i X j).trace :=
  Finset.sum_congr rfl fun a _ => blockDirection_apply_same B i X j a a

private theorem hasDerivAt_singleBlockInParabolic_entry {R : Type*}
    [NormedCommRing R] [NormedAlgebra ℝ R] (i : Fin B.length)
    {γ : ℝ → Langlands.GeneralLinear (B.size i) R}
    {X : Matrix (Fin (B.size i)) (Fin (B.size i)) R}
    (hγ : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (X a b) 0) (a b : Fin n) :
    HasDerivAt (fun t => (B.singleBlockInParabolic R i (γ t)).val.val a b)
      (blockDirection B i X a b) 0 := by
  obtain ⟨⟨j, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨k, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change HasDerivAt
    (fun t => B.leviEmbedding R (Pi.mulSingle i (γ t)) (B.index j a) (B.index k b))
    (blockDirection B i X (B.index j a) (B.index k b)) 0
  by_cases hjk : j = k
  · subst k
    simp_rw [B.leviEmbedding_apply_same, blockDirection_apply_same]
    by_cases hji : j = i
    · subst j
      simpa only [Pi.mulSingle_eq_same, Pi.single_eq_same] using hγ a b
    · simp only [Pi.mulSingle_eq_of_ne hji, Pi.single_eq_of_ne hji, Matrix.zero_apply]
      exact hasDerivAt_const _ _
  · simp_rw [B.leviEmbedding_apply_ne R _ a b hjk, blockDirection_apply_ne B i X hjk a b]
    exact hasDerivAt_const _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

private theorem hasDerivAt_inverseHalfBlock_real (v : RP) (i : Fin B.length)
    {γ : ℝ → Langlands.GeneralLinear (B.size i) ℝ}
    {X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℝ}
    (h0 : γ 0 = 1) (hγ : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (X a b) 0) :
    HasDerivAt (fun t => ((inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
      (AdelicGL.realPlaceInclusion F (B.size i) v (γ t)) : ℂ))
      (-(blockHalfExponent B.size i * X.trace : ℝ) : ℂ) 0 := by
  let p t := B.singleBlockInParabolic ℝ i (γ t)
  have hp : p 0 = 1 := by simp [p, h0]
  have hd := hasDerivAt_parabolicHalfCharacter_realPlace B F v hp
    (hasDerivAt_singleBlockInParabolic_entry B i hγ)
  have hs : (∑ j, blockHalfExponent B.size j * blockTrace B (blockDirection B i X) j) =
      blockHalfExponent B.size i * X.trace := by
    simp_rw [blockTrace_blockDirection]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [hs] at hd
  have h := hd.inv (show (parabolicHalfCharacter F B (realPlaceInclusion F B v (p 0)) : ℂ) ≠ 0
    from Units.ne_zero _)
  simp_rw [inverseHalfBlockHeckeCharacter_realPlace, Units.val_inv_eq_inv_val]
  simpa [p, hp] using! h

private theorem hasDerivAt_inverseHalfBlock_complex (v : CP) (i : Fin B.length)
    {γ : ℝ → Langlands.GeneralLinear (B.size i) ℂ}
    {X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ}
    (h0 : γ 0 = 1) (hγ : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (X a b) 0) :
    HasDerivAt (fun t => ((inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
      (AdelicGL.complexPlaceInclusion F (B.size i) v (γ t)) : ℂ))
      (-(blockHalfExponent B.size i * (2 * X.trace.re) : ℝ) : ℂ) 0 := by
  let p t := B.singleBlockInParabolic ℂ i (γ t)
  have hp : p 0 = 1 := by simp [p, h0]
  have hd := hasDerivAt_parabolicHalfCharacter_complexPlace B F v hp
    (hasDerivAt_singleBlockInParabolic_entry B i hγ)
  have hs : (∑ j, blockHalfExponent B.size j * (2 * (blockTrace B (blockDirection B i X) j).re)) =
      blockHalfExponent B.size i * (2 * X.trace.re) := by
    simp_rw [blockTrace_blockDirection]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [hs] at hd
  have h := hd.inv (show (parabolicHalfCharacter F B (complexPlaceInclusion F B v (p 0)) : ℂ) ≠ 0
    from Units.ne_zero _)
  simp_rw [inverseHalfBlockHeckeCharacter_complexPlace, Units.val_inv_eq_inv_val]
  simpa [p, hp] using! h

section Chart

variable {d : ℕ}

omit [NumberField F] in
private theorem coordinates_realPlaceGL (v : RP) (g : Langlands.GeneralLinear d ℝ) :
    (realPlaceGL F d v g : ArchimedeanMatrix F d) =
      realPlaceMatrixInsertion v (Matrix.of.symm g.val) + realPlaceMatrixBase v := by
  classical
  refine Matrix.ext fun a b => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change ((Pi.mulSingle v g : RP → Langlands.GeneralLinear d ℝ) w).val a b = _
    by_cases hw : w = v
    · subst w
      simp [realPlaceMatrixInsertion, realPlaceMatrixBase]
    · simp [realPlaceMatrixInsertion, realPlaceMatrixBase, hw]
  · change (1 : Matrix (Fin d) (Fin d) ℂ) a b = _
    simp [realPlaceMatrixInsertion, realPlaceMatrixBase]

omit [NumberField F] in
private theorem coordinates_complexPlaceGL (v : CP) (g : Langlands.GeneralLinear d ℂ) :
    (complexPlaceGL F d v g : ArchimedeanMatrix F d) =
      complexPlaceMatrixInsertion v (Matrix.of.symm g.val) + complexPlaceMatrixBase v := by
  classical
  refine Matrix.ext fun a b => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change (1 : Matrix (Fin d) (Fin d) ℝ) a b = _
    simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase]
  · change ((Pi.mulSingle v g : CP → Langlands.GeneralLinear d ℂ) w).val a b = _
    by_cases hw : w = v
    · subst w
      simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase]
    · simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase, hw]

private theorem hasDerivAt_coordinates_realPlaceGL (v : RP)
    {γ : ℝ → Langlands.GeneralLinear d ℝ} {X : Matrix (Fin d) (Fin d) ℝ}
    (hγ : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (X a b) 0) :
    HasDerivAt (fun t => (realPlaceGL F d v (γ t) : ArchimedeanMatrix F d))
      (realLieAlgebraToMatrix F d (realPlaceLieInclusion F d v X)) 0 := by
  have hg : HasDerivAt (fun t => Matrix.of.symm (γ t).val) (Matrix.of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hγ a b
  have h := ((LinearMap.toContinuousLinearMap
    (realPlaceMatrixInsertion (F := F) (n := d) v)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hg).add_const (realPlaceMatrixBase v)
  simp_rw [coordinates_realPlaceGL, realLieAlgebraToMatrix_realPlaceLieInclusion]
  exact h

private theorem hasDerivAt_coordinates_complexPlaceGL (v : CP)
    {γ : ℝ → Langlands.GeneralLinear d ℂ} {X : Matrix (Fin d) (Fin d) ℂ}
    (hγ : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (X a b) 0) :
    HasDerivAt (fun t => (complexPlaceGL F d v (γ t) : ArchimedeanMatrix F d))
      (realLieAlgebraToMatrix F d (complexPlaceLieInclusion F d v X)) 0 := by
  have hg : HasDerivAt (fun t => Matrix.of.symm (γ t).val) (Matrix.of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hγ a b
  have h := ((LinearMap.toContinuousLinearMap
    (complexPlaceMatrixInsertion (F := F) (n := d) v)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hg).add_const (complexPlaceMatrixBase v)
  simp_rw [coordinates_complexPlaceGL, realLieAlgebraToMatrix_complexPlaceLieInclusion]
  exact h

private theorem hasDerivAt_infiniteDeterminantCharacter_curve (χ : HeckeCharacter F)
    {γ : ℝ → ArchimedeanGL F d} {X : RealLieAlgebra F d}
    (h0 : γ 0 = 1)
    (hγ : HasDerivAt (fun t => (γ t : ArchimedeanMatrix F d)) (realLieAlgebraToMatrix F d X) 0) :
    HasDerivAt (fun t => (χ.infiniteDeterminantCharacter d ((archimedeanGLCoordinates F d).symm
      (γ t)) : ℂ))
      (characterDifferential (χ.infiniteDeterminantCharacter d)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions d) X) 0 := by
  let f := characterFunction (χ.infiniteDeterminantCharacter d)
    (χ.infiniteDeterminantCharacter_mem_smoothFunctions d)
  have hf := ((coordinateExtension_contDiffAt F d f (1 : ArchimedeanGL F d)).differentiableAt
    (by simp)).hasFDerivAt
  have hbase : (γ 0 : ArchimedeanMatrix F d) = 1 := by rw [h0, Units.val_one]
  rw [Units.val_one, ← hbase] at hf
  have h := hf.comp_hasDerivAt 0 hγ
  change HasDerivAt _ ((smoothDifferential F d X f).val 1) 0
  rw [smoothDifferential_apply, map_one, Units.val_one, one_mul]
  rw [hbase] at h
  convert h using 1
  funext t
  rw [Function.comp_apply, coordinateExtension_apply, characterFunction_apply]

end Chart

/-- Scalar shift in the real-place Lie action of the inverse half-modulus twist. -/
theorem inverseHalfBlockHeckeCharacter_differential_realPlace (v : RP) (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℝ) :
    characterDifferential ((inverseHalfBlockHeckeCharacter F B i).infiniteDeterminantCharacter
        (B.size i))
      ((inverseHalfBlockHeckeCharacter F B i).infiniteDeterminantCharacter_mem_smoothFunctions
        (B.size i)) (realPlaceLieInclusion F (B.size i) v X) =
      (-(blockHalfExponent B.size i * X.trace : ℝ) : ℂ) := by
  let γ := matrixExponentialCurve X
  have hγ := hasDerivAt_matrixExponentialCurve_entry X
  have hd := hasDerivAt_infiniteDeterminantCharacter_curve F (inverseHalfBlockHeckeCharacter F B i)
    (γ := fun t => realPlaceGL F (B.size i) v (γ t)) (by simp [γ])
    (hasDerivAt_coordinates_realPlaceGL F v hγ)
  exact hd.unique (hasDerivAt_inverseHalfBlock_real B F v i (by simp [γ]) hγ)

/-- Scalar shift in the complex-place Lie action of the inverse half-modulus twist. -/
theorem inverseHalfBlockHeckeCharacter_differential_complexPlace (v : CP) (i : Fin B.length)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ) :
    characterDifferential ((inverseHalfBlockHeckeCharacter F B i).infiniteDeterminantCharacter
        (B.size i))
      ((inverseHalfBlockHeckeCharacter F B i).infiniteDeterminantCharacter_mem_smoothFunctions
        (B.size i)) (complexPlaceLieInclusion F (B.size i) v X) =
      (-(blockHalfExponent B.size i * (2 * X.trace.re) : ℝ) : ℂ) := by
  let γ := matrixExponentialCurve X
  have hγ := hasDerivAt_matrixExponentialCurve_entry X
  have hd := hasDerivAt_infiniteDeterminantCharacter_curve F (inverseHalfBlockHeckeCharacter F B i)
    (γ := fun t => complexPlaceGL F (B.size i) v (γ t)) (by simp [γ])
    (hasDerivAt_coordinates_complexPlaceGL F v hγ)
  exact hd.unique (hasDerivAt_inverseHalfBlock_complex B F v i (by simp [γ]) hγ)

section OperatorActions

local instance (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance (d : ℕ) : AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance {d : ℕ} (S : OperatorRealization F d) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable (i : Fin B.length) (S : OperatorRealization F (B.size i))

local notation "χ" => inverseHalfBlockHeckeCharacter F B i
local notation "E" => S.heckeDeterminantTwistEquiv χ

private theorem inverseHalfBlock_generator (X : RealLieAlgebra F (B.size i)) :
    heckeEnvelopingShift (B.size i) χ (envelopingGenerator F (B.size i)
      (complexify F (B.size i) X)) =
    envelopingGenerator F (B.size i) (complexify F (B.size i) X) +
      algebraMap ℂ (EnvelopingAlgebra F (B.size i))
        (characterDifferential ((χ).infiniteDeterminantCharacter (B.size i))
          ((χ).infiniteDeterminantCharacter_mem_smoothFunctions (B.size i)) X) := by
  simp [heckeEnvelopingShift, characterShift, complexify_apply]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The inverse half-modulus twist shifts the real-place Lie action by the
negative outer exponent times the trace. -/
theorem realPlaceLieAction_inverseHalfBlockTwist (v : RP)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℝ) (w : S.Space) :
    (S.heckeDeterminantTwist χ).realPlaceLieAction v (1 ⊗ₜ X) (E w) =
      E (S.realPlaceLieAction v (1 ⊗ₜ X) w -
        (↑(blockHalfExponent B.size i * X.trace) : ℂ) • w) := by
  let Y := realPlaceLieInclusion F (B.size i) v X
  have hg := (inverseHalfBlock_generator B F i Y).trans
    (congrArg (fun a : ℂ => envelopingGenerator F (B.size i) (complexify F (B.size i) Y) +
      algebraMap ℂ (EnvelopingAlgebra F (B.size i)) a)
      (inverseHalfBlockHeckeCharacter_differential_realPlace B F v i X))
  have h := S.lieAction_heckeDeterminantTwistEquiv χ Y hg w
  simpa only [OperatorRealization.realPlaceLieAction_apply, realPlaceComplexLieInclusion_tmul,
    sub_eq_add_neg, Complex.ofReal_neg, neg_smul] using! h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The inverse half-modulus twist shifts the complex-place Lie action by the
negative outer exponent times twice the real part of the trace. -/
theorem complexPlaceLieAction_inverseHalfBlockTwist (v : CP)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ) (w : S.Space) :
    (S.heckeDeterminantTwist χ).complexPlaceLieAction v (1 ⊗ₜ X) (E w) =
      E (S.complexPlaceLieAction v (1 ⊗ₜ X) w -
        (↑(blockHalfExponent B.size i * (2 * X.trace.re)) : ℂ) • w) := by
  let Y := complexPlaceLieInclusion F (B.size i) v X
  have hg := (inverseHalfBlock_generator B F i Y).trans
    (congrArg (fun a : ℂ => envelopingGenerator F (B.size i) (complexify F (B.size i) Y) +
      algebraMap ℂ (EnvelopingAlgebra F (B.size i)) a)
      (inverseHalfBlockHeckeCharacter_differential_complexPlace B F v i X))
  have h := S.lieAction_heckeDeterminantTwistEquiv χ Y hg w
  simpa only [OperatorRealization.complexPlaceLieAction_apply, complexPlaceComplexLieInclusion_tmul,
    sub_eq_add_neg, Complex.ofReal_neg, neg_smul] using! h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 600000 in
/-- The inverse half-modulus twist preserves the compact action at a real place. -/
theorem realPlaceCompactRepresentation_inverseHalfBlockTwist (v : RP)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℝ) (w : S.Space) :
    (S.heckeDeterminantTwist χ).realPlaceCompactRepresentation v k (E w) =
      E (S.realPlaceCompactRepresentation v k w) := by
  let l := realPlaceCompactInclusion F (B.size i) v k
  have hl : archimedeanGLCoordinates F (B.size i) l.val =
      realPlaceGL F (B.size i) v (Unitary.toUnits k) := by
    apply Units.ext
    rw [coordinates_realPlaceCompactInclusion, coordinates_realPlaceGL]
    rfl
  have hpos : AdelicGL.ofInfinite F (B.size i) l.val =
      AdelicGL.realPlaceInclusion F (B.size i) v (Unitary.toUnits k) := by
    change _ = AdelicGL.ofInfinite F (B.size i) ((archimedeanGLCoordinates F (B.size i)).symm
      (realPlaceGL F (B.size i) v (Unitary.toUnits k)))
    rw [← hl, ContinuousMulEquiv.symm_apply_apply]
  have hs : ((χ).adelicDeterminant (B.size i) (AdelicGL.ofInfinite F (B.size i) l.val) : ℂ) = 1 :=
    (congrArg (fun g => ((χ).adelicDeterminant (B.size i) g : ℂ)) hpos).trans
      (inverseHalfBlockHeckeCharacter_realPlace_compact F B v i k)
  calc
    _ = ((χ).adelicDeterminant (B.size i) (AdelicGL.ofInfinite F (B.size i) l.val) : ℂ) •
        E (S.realPlaceCompactRepresentation v k w) := S.heckeDeterminantTwistEquiv_compact χ l w
    _ = _ := (congrArg (fun a : ℂ => a • E (S.realPlaceCompactRepresentation v k w)) hs).trans
      (one_smul ℂ _)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 600000 in
/-- The inverse half-modulus twist preserves the compact action at a complex place. -/
theorem complexPlaceCompactRepresentation_inverseHalfBlockTwist (v : CP)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℂ) (w : S.Space) :
    (S.heckeDeterminantTwist χ).complexPlaceCompactRepresentation v k (E w) =
      E (S.complexPlaceCompactRepresentation v k w) := by
  let l := complexPlaceCompactInclusion F (B.size i) v k
  have hl : archimedeanGLCoordinates F (B.size i) l.val =
      complexPlaceGL F (B.size i) v (Unitary.toUnits k) := by
    apply Units.ext
    rw [coordinates_complexPlaceCompactInclusion, coordinates_complexPlaceGL]
    rfl
  have hpos : AdelicGL.ofInfinite F (B.size i) l.val =
      AdelicGL.complexPlaceInclusion F (B.size i) v (Unitary.toUnits k) := by
    change _ = AdelicGL.ofInfinite F (B.size i) ((archimedeanGLCoordinates F (B.size i)).symm
      (complexPlaceGL F (B.size i) v (Unitary.toUnits k)))
    rw [← hl, ContinuousMulEquiv.symm_apply_apply]
  have hs : ((χ).adelicDeterminant (B.size i) (AdelicGL.ofInfinite F (B.size i) l.val) : ℂ) = 1 :=
    (congrArg (fun g => ((χ).adelicDeterminant (B.size i) g : ℂ)) hpos).trans
      (inverseHalfBlockHeckeCharacter_complexPlace_compact F B v i k)
  calc
    _ = ((χ).adelicDeterminant (B.size i) (AdelicGL.ofInfinite F (B.size i) l.val) : ℂ) •
        E (S.complexPlaceCompactRepresentation v k w) := S.heckeDeterminantTwistEquiv_compact χ l w
    _ = _ := (congrArg (fun a : ℂ => a • E (S.complexPlaceCompactRepresentation v k w)) hs).trans
      (one_smul ℂ _)

end OperatorActions

end Langlands.Global.FiniteParametrizedBlockInduction
