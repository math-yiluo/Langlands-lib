import Langlands.Automorphic.BlockShapeLeviSliceRegularity
import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter

/-! # Differential operators of an individual Levi block -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MeasureTheory Topology
open scoped Classical TensorProduct CategoryTheory.MonObj Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear
  Global.RankinSelbergGlobal.WhittakerCurve

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

private def archimedeanLeviMatrixRingHom :
    (∀ j, ArchimedeanMatrix F (B.size j)) →+* ArchimedeanMatrix F n :=
  (Matrix.reindexRingEquiv (mixedEmbedding.mixedSpace F) B.indexEquiv).toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun j => Fin (B.size j)) _)

private def archimedeanLeviMatrixLinearMap :
    (∀ j, ArchimedeanMatrix F (B.size j)) →ₗ[ℝ] ArchimedeanMatrix F n where
  toFun := archimedeanLeviMatrixRingHom F B
  map_add' := map_add _
  map_smul' c M := by
    change Matrix.reindex _ _ (Matrix.blockDiagonal' (c • M)) =
      c • Matrix.reindex _ _ (Matrix.blockDiagonal' M)
    rw [Matrix.blockDiagonal'_smul]
    rfl

private theorem archimedeanLeviMatrixRingHom_continuous :
    Continuous (archimedeanLeviMatrixRingHom F B) :=
  (archimedeanLeviMatrixLinearMap F B).toContinuousLinearMap.continuous

variable (i : Fin B.length)

omit [NumberField F] in
private theorem archimedeanBlockMatrixInclusion_apply (X : ArchimedeanMatrix F (B.size i)) :
    archimedeanBlockMatrixInclusion F B i X =
      archimedeanLeviMatrixRingHom F B (Pi.single i X) := rfl

omit [NumberField F] in
private theorem archimedeanBlockMatrixInclusion_mul (X Y : ArchimedeanMatrix F (B.size i)) :
    archimedeanBlockMatrixInclusion F B i (X * Y) =
      archimedeanBlockMatrixInclusion F B i X * archimedeanBlockMatrixInclusion F B i Y := by
  have h : Pi.single i (X * Y) = (Pi.single i X * Pi.single i Y :
      ∀ j, ArchimedeanMatrix F (B.size j)) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mul_apply, Pi.single_eq_same]
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero]
  simp only [archimedeanBlockMatrixInclusion_apply, h, map_mul]

/-- The real Lie inclusion given by the linear part of the matrix block
embedding. -/
def blockShapeRealLieInclusion :
    RealLieAlgebra F (B.size i) →ₗ⁅ℝ⁆ RealLieAlgebra F n :=
  { (realLieAlgebraToMatrix F n).symm.toLinearMap ∘ₗ
      archimedeanBlockMatrixInclusion F B i ∘ₗ
      (realLieAlgebraToMatrix F (B.size i)).toLinearMap with
    map_lie' := fun {X Y} => by
      apply (realLieAlgebraToMatrix F n).injective
      let L := archimedeanBlockMatrixInclusion F B i
      let x := realLieAlgebraToMatrix F (B.size i) X
      let y := realLieAlgebraToMatrix F (B.size i) Y
      change L (x * y - y * x) = L x * L y - L y * L x
      rw [map_sub, archimedeanBlockMatrixInclusion_mul, archimedeanBlockMatrixInclusion_mul] }

omit [NumberField F] in
theorem blockShapeRealLieInclusion_matrix (X : RealLieAlgebra F (B.size i)) :
    realLieAlgebraToMatrix F n (blockShapeRealLieInclusion F B i X) =
      archimedeanBlockMatrixInclusion F B i (realLieAlgebraToMatrix F (B.size i) X) :=
  (realLieAlgebraToMatrix F n).apply_symm_apply _

/-- The same inclusion on the genuine complex Lie algebras. -/
def blockShapeComplexLieInclusion :
    ComplexLieAlgebra F (B.size i) →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  { (blockShapeRealLieInclusion F B i).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (blockShapeRealLieInclusion F B i)).map_lie X Y }

omit [NumberField F] in
theorem blockShapeComplexLieInclusion_complexify (X : RealLieAlgebra F (B.size i)) :
    blockShapeComplexLieInclusion F B i (complexify F (B.size i) X) =
      complexify F n (blockShapeRealLieInclusion F B i X) := rfl

/-- The actual inclusion of block enveloping operators. -/
def blockShapeEnvelopingInclusion : EnvelopingAlgebra F (B.size i) →ₐ[ℂ] EnvelopingAlgebra F n :=
  Langlands.Algebra.LieEnvelopingEquiv.map (blockShapeComplexLieInclusion F B i)

theorem oneParameter_blockShapeRealLieInclusion (X : RealLieAlgebra F (B.size i)) (t : ℝ) :
    oneParameter F n (blockShapeRealLieInclusion F B i X) t =
      blockShapeSingleEmbedding B (mixedEmbedding.mixedSpace F) i
        (oneParameter F (B.size i) X t) := by
  apply Units.ext
  let M := realLieAlgebraToMatrix F (B.size i) X
  let L := archimedeanLeviMatrixRingHom F B
  let P : ∀ j, ArchimedeanMatrix F (B.size j) := Pi.single i (t • M)
  have hP : P = t • Pi.single i M := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [P, Pi.smul_apply, Pi.single_eq_same]
    · simp only [P, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
  have hLP : L P = t • archimedeanBlockMatrixInclusion F B i M := by
    rw [hP]
    exact (archimedeanLeviMatrixLinearMap F B).map_smul t (Pi.single i M)
  have hExp : NormedSpace.exp P = fun j =>
      (Pi.mulSingle i (oneParameter F (B.size i) X t) :
        B.Levi (mixedEmbedding.mixedSpace F)) j |>.val := by
    funext j
    rw [Pi.coe_exp]
    by_cases hj : j = i
    · subst j
      simp only [P, M, Pi.single_eq_same, Pi.mulSingle_eq_same, oneParameter_val]
    · simp only [P, Pi.single_eq_of_ne hj, NormedSpace.exp_zero, Pi.mulSingle_eq_of_ne hj,
        Units.val_one]
  rw [oneParameter_val, blockShapeRealLieInclusion_matrix, ← hLP,
    ← NormedSpace.map_exp L (archimedeanLeviMatrixRingHom_continuous F B), hExp]
  rfl

private theorem leviEmbedding_map {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
    (m : B.Levi A) :
    Matrix.GeneralLinearGroup.map f (B.leviEmbedding A m) =
      B.leviEmbedding C (fun j => Matrix.GeneralLinearGroup.map f (m j)) := by
  apply Units.ext
  change ((Matrix.blockDiagonal' (fun j => (m j).val)).map f).submatrix
    B.indexEquiv.symm B.indexEquiv.symm =
    (Matrix.blockDiagonal' (fun j => ((Matrix.GeneralLinearGroup.map f) (m j)).val)).submatrix
      B.indexEquiv.symm B.indexEquiv.symm
  rw [Matrix.blockDiagonal'_map _ _ (map_zero f)]
  rfl

private theorem blockShapeSingleEmbedding_map {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) (x : GeneralLinear (B.size i) A) :
    Matrix.GeneralLinearGroup.map f (blockShapeSingleEmbedding B A i x) =
      blockShapeSingleEmbedding B C i (Matrix.GeneralLinearGroup.map f x) := by
  change Matrix.GeneralLinearGroup.map f (B.leviEmbedding A (Pi.mulSingle i x)) =
    B.leviEmbedding C (Pi.mulSingle i (Matrix.GeneralLinearGroup.map f x))
  rw [leviEmbedding_map B f]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
  · simp only [Pi.mulSingle_eq_of_ne hj, map_one]

theorem infiniteOneParameter_blockShapeRealLieInclusion (X : RealLieAlgebra F (B.size i)) (t : ℝ) :
    infiniteOneParameter F n (blockShapeRealLieInclusion F B i X) t =
      blockShapeSingleEmbedding B (InfiniteAdeleRing F) i (infiniteOneParameter F (B.size i) X t) := by
  rw [infiniteOneParameter, oneParameter_blockShapeRealLieInclusion]
  exact blockShapeSingleEmbedding_map B i
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom (oneParameter F (B.size i) X t)

private theorem blockShapeSingleEmbedding_ofInfinite (a : InfiniteAdelicGL F (B.size i)) :
    blockShapeSingleEmbedding B (Adeles F) i (AdelicGL.ofInfinite F (B.size i) a) =
      AdelicGL.ofInfinite F n (blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a) := by
  let x := AdelicGL.ofInfinite F (B.size i) a
  have hInf : AdelicGL.infinite F n (blockShapeSingleEmbedding B (Adeles F) i x) =
      blockShapeSingleEmbedding B (InfiniteAdeleRing F) i (AdelicGL.infinite F (B.size i) x) :=
    blockShapeSingleEmbedding_map B i
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x
  have hFin : AdelicGL.finite F n (blockShapeSingleEmbedding B (Adeles F) i x) =
      blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i (AdelicGL.finite F (B.size i) x) :=
    blockShapeSingleEmbedding_map B i
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x
  apply AdelicGL.ext_infinite_finite F n
  · rw [hInf]
    simp only [x, AdelicGL.infinite_ofInfinite]
  · rw [hFin]
    simp only [x, AdelicGL.finite_ofInfinite, map_one]

local instance blockSliceDifferentialRationalAddCommGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance blockSliceDifferentialContinuousAddCommGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance blockSliceDifferentialFiniteAddCommGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _

/-- At the identity ambient argument, the individual finite-smooth slice
depends linearly on the original finite-smooth function. -/
def blockShapeLeviSliceFactorLinearMap (m : AdelicBlockParabolic.FullLevi F B) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] FiniteSmoothRationalFunctions F (B.size i) where
  toFun f := blockShapeFiniteSmoothLeviSliceFactor F B i f 1 m
  map_add' f h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun (map_add (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) f h)
      ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (B.leviEmbedding (Adeles F) (Function.update m i x) * 1))
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun (map_smul (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) c f)
      ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (B.leviEmbedding (Adeles F) (Function.update m i x) * 1))

private theorem hasDerivAt_finiteSmooth_adelicOneParameter (d : ℕ) (X : RealLieAlgebra F d)
    (f : FiniteSmoothRationalFunctions F d) (x : AdelicGL F d) :
    HasDerivAt (fun t => ContinuousRationalFunctions.evaluate F d f.val
      (x * AdelicGL.ofInfinite F d (infiniteOneParameter F d X t)))
      (ContinuousRationalFunctions.evaluate F d
        (finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)) f).val x) 0 := by
  have h := hasDerivAt_smooth_oneParameter F d (finiteSmoothSlice F d (AdelicGL.finite F d x) f)
    X (AdelicGL.infinite F d x) 0
  simp only [infiniteOneParameter_zero, mul_one] at h
  rw [← envelopingAction_real_generator, ← finiteSmoothSlice_envelopingAction] at h
  simpa only [finiteSmoothSlice_apply, OperatorRealization.mul_ofInfinite_eq_pair,
    AdelicGL.pair_projections] using h

set_option maxHeartbeats 800000 in
private theorem blockSlice_realGenerator (m : AdelicBlockParabolic.FullLevi F B)
    (X : RealLieAlgebra F (B.size i)) (f : FiniteSmoothRationalFunctions F n) :
    blockShapeLeviSliceFactorLinearMap F B i m
      (finiteSmoothEnvelopingAction F n
        (envelopingGenerator F n (complexify F n (blockShapeRealLieInclusion F B i X))) f) =
      finiteSmoothEnvelopingAction F (B.size i)
        (envelopingGenerator F (B.size i) (complexify F (B.size i) X))
        (blockShapeLeviSliceFactorLinearMap F B i m f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let E := GeneralLinearGroupPoints.adelicEquiv F n
  let Y := blockShapeRealLieInclusion F B i X
  let z := B.leviEmbedding (Adeles F) (Function.update m i x)
  let w := standardBlockWeight B.cuts
  let D := finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n Y)) f
  let s := blockShapeLeviSliceFactorLinearMap F B i m f
  let a (t : ℝ) := AdelicGL.ofInfinite F (B.size i) (infiniteOneParameter F (B.size i) X t)
  have he (t : ℝ) : E (adelicOneParameter F n Y t) =
      blockShapeSingleEmbedding B (Adeles F) i (a t) := by
    change E (E.symm (AdelicGL.ofInfinite F n (infiniteOneParameter F n Y t))) = _
    rw [E.apply_symm_apply, infiniteOneParameter_blockShapeRealLieInclusion,
      blockShapeSingleEmbedding_ofInfinite]
  have hcurve (t : ℝ) :
      finiteSmoothBlockConstantTerm F w f (E.symm z * adelicOneParameter F n Y t) =
        ContinuousRationalFunctions.evaluate F (B.size i) s.val (x * a t) := by
    have hcoord : Function.update m i (x * a t) =
        Function.update m i x * Pi.mulSingle i (a t) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same]
      · simp only [Function.update_of_ne hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, mul_one]
    have harg : E.symm z * adelicOneParameter F n Y t =
        E.symm (B.leviEmbedding (Adeles F) (Function.update m i (x * a t))) := by
      apply E.injective
      rw [map_mul, E.apply_symm_apply, he, E.apply_symm_apply, hcoord, map_mul]
      rfl
    rw [harg]
    change _ = finiteSmoothBlockConstantTerm F w f
      (E.symm (B.leviEmbedding (Adeles F) (Function.update m i (x * a t)) * 1))
    rw [mul_one]
  have hct := finiteSmoothBlockConstantTerm_hasDerivAt F w Y f (E.symm z) 0
  have hzero : adelicOneParameter F n Y 0 = 1 := by
    simp only [adelicOneParameter, infiniteOneParameter_zero, map_one]
  have hct' : HasDerivAt (fun t => ContinuousRationalFunctions.evaluate F (B.size i) s.val
      (x * a t)) (finiteSmoothBlockConstantTerm F w D (E.symm z)) 0 := by
    rwa [show (fun t => finiteSmoothBlockConstantTerm F w f
      (E.symm z * adelicOneParameter F n Y t)) = _ from funext hcurve, hzero, mul_one] at hct
  have hd := hct'.unique (hasDerivAt_finiteSmooth_adelicOneParameter F (B.size i) X s x)
  change finiteSmoothBlockConstantTerm F w D (E.symm (z * 1)) = _
  rw [mul_one]
  exact hd

/-- Differentiation inside a single Levi block is the action of the
corresponding ambient enveloping operator before taking the slice. -/
theorem blockShapeLeviSliceFactor_enveloping (m : AdelicBlockParabolic.FullLevi F B)
    (u : EnvelopingAlgebra F (B.size i)) (f : FiniteSmoothRationalFunctions F n) :
    blockShapeLeviSliceFactorLinearMap F B i m
      (finiteSmoothEnvelopingAction F n (blockShapeEnvelopingInclusion F B i u) f) =
      finiteSmoothEnvelopingAction F (B.size i) u
        (blockShapeLeviSliceFactorLinearMap F B i m f) := by
  let A := finiteSmoothEnvelopingAction F n
  let C := finiteSmoothEnvelopingAction F (B.size i)
  let L := blockShapeLeviSliceFactorLinearMap F B i m
  let J := blockShapeEnvelopingInclusion F B i
  let D := blockShapeComplexLieInclusion F B i
  let a := envelopingGenerator F n
  let b := envelopingGenerator F (B.size i)
  have hgen (X : ComplexLieAlgebra F (B.size i)) :
      ∀ f, L (A (a (D X)) f) = C (b X) (L f) := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      intro f
      have hX : c ⊗ₜ[ℝ] X = c • complexify F (B.size i) X := by
        simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hX]
      simp only [map_smul, LinearMap.smul_apply]
      rw [show D (complexify F (B.size i) X) =
        complexify F n (blockShapeRealLieInclusion F B i X) from
        blockShapeComplexLieInclusion_complexify F B i X]
      exact congrArg (c • ·) (blockSlice_realGenerator F B i m X f)
    | add X Y hX hY =>
      intro f
      simp only [map_add, LinearMap.add_apply, hX f, hY f]
  change L (A (J u) f) = C u (L f)
  revert f
  induction u using Langlands.Archimedean.InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    intro f
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_smul, map_one]
  | «ι» X =>
    intro f
    have hJ : J (b X) = a (D X) := Langlands.Algebra.LieEnvelopingEquiv.map_generator D X
    change L (A (J (b X)) f) = C (b X) (L f)
    rw [hJ]
    exact hgen X f
  | mul u v hu hv =>
    intro f
    simp only [map_mul, Module.End.mul_apply, hu, hv]
  | add u v hu hv =>
    intro f
    simp only [map_add, LinearMap.add_apply, hu, hv]

end Langlands.Automorphic
