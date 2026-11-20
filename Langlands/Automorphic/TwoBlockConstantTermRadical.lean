import Langlands.Automorphic.TwoBlockConstantTermSmooth
import Langlands.Automorphic.TwoBlockConstantTermActions
import Langlands.Automorphic.CuspidalL2.Decay

/-! # The infinitesimal upper radical annihilates constant-term evaluation on the Levi -/

noncomputable section
universe u

open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear

variable {R : Type u} [CommRing R] {a b n : ℕ} (h : a + b = n)

/-- Conjugation by the block diagonal group acts on the upper block radical. -/
theorem blockDiagonalEmbedding_mul_blockUnipotent
    (z : GeneralLinear a R × GeneralLinear b R) (X : Matrix (Fin a) (Fin b) R) :
    blockDiagonalEmbedding h z * blockUnipotent h X =
      blockUnipotent h (z.1.val * X * z.2⁻¹.val) * blockDiagonalEmbedding h z := by
  have he := blockUnipotent_mul_blockDiagonalEmbedding h z (z.1.val * X * z.2⁻¹.val)
  have hx : z.1⁻¹.val * (z.1.val * X * z.2⁻¹.val) * z.2.val = X := by
    rw [← Matrix.mul_assoc z.1⁻¹.val, ← Matrix.mul_assoc z.1⁻¹.val, Units.inv_mul,
      Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [hx] at he
  exact he.symm

end Langlands.GeneralLinear

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ArchimedeanGL NumberField

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "Rect" => Matrix (Fin a) (Fin b) (mixedEmbedding.mixedSpace F)
local notation "M" => ArchimedeanMatrix F n

/-- The upper off-diagonal block regarded as a real Lie direction. -/
def upperBlockLieDirection (X : Rect) : RealLieAlgebra F n :=
  (realLieAlgebraToMatrix F n).symm
    (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks 0 X 0 0))

omit [NumberField F] in
private theorem blockUnipotent_smul_val (X : Rect) (t : ℝ) :
    (blockUnipotent h (t • X)).val =
      (1 : M) + t • realLieAlgebraToMatrix F n (upperBlockLieDirection F h X) := by
  let e := finSumFinEquiv.trans (finCongr h)
  have hs : Matrix.fromBlocks (0 : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace F))
      (t • X) 0 (0 : Matrix (Fin b) (Fin b) (mixedEmbedding.mixedSpace F)) =
      t • Matrix.fromBlocks 0 X 0 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero, smul_zero, smul_zero]
  have he := blockUnipotent_val_sub_one h (t • X)
  rw [hs, ← Matrix.coe_reindexLinearEquiv ℝ (mixedEmbedding.mixedSpace F) e e, map_smul] at he
  rw [upperBlockLieDirection, LinearEquiv.apply_symm_apply]
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

private theorem ofInfinite_blockUnipotent
    (X : Matrix (Fin a) (Fin b) (InfiniteAdeles F)) :
    AdelicGL.ofInfinite F n (blockUnipotent h X) =
      blockUnipotent h (X.map fun y => (y, (0 : FiniteAdeles F))) := by
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n _ = AdelicGL.infinite F n _
    rw [AdelicGL.infinite_ofInfinite]
    change blockUnipotent h X =
      Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F))
        (blockUnipotent h _)
    rw [map_blockUnipotent]
    rfl
  · change AdelicGL.finite F n _ = AdelicGL.finite F n _
    rw [AdelicGL.finite_ofInfinite]
    change 1 = Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F))
      (blockUnipotent h _)
    rw [map_blockUnipotent, show
      (X.map fun y => (y, (0 : FiniteAdeles F))).map
        (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F)) = 0 from rfl,
      blockUnipotent_zero]

variable [CompactSpace (AdeleQuotient F)]

private theorem constantTerm_pair_mul_blockUnipotent
    (f : ContinuousRationalFunctions F n) (d : FiniteAdelicGL F n)
    (z : InfiniteAdelicGL F a × InfiniteAdelicGL F b)
    (X : Matrix (Fin a) (Fin b) (InfiniteAdeles F)) :
    constantTerm F n h f
      (AdelicGL.pair F n (blockDiagonalEmbedding h z * blockUnipotent h X) d) =
        constantTerm F n h f (AdelicGL.pair F n (blockDiagonalEmbedding h z) d) := by
  rw [blockDiagonalEmbedding_mul_blockUnipotent]
  let Y := z.1.val * X * z.2⁻¹.val
  have he : AdelicGL.pair F n (blockUnipotent h Y * blockDiagonalEmbedding h z) d =
      AdelicGL.ofInfinite F n (blockUnipotent h Y) *
        AdelicGL.pair F n (blockDiagonalEmbedding h z) d := by
    rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, one_mul]
  rw [he, ofInfinite_blockUnipotent, constantTerm_blockUnipotent_mul]

set_option maxHeartbeats 800000 in
/-- At every point of the infinite block diagonal group and every finite argument, the
constant term of a source function differentiated in a real upper radical direction
vanishes. -/
theorem constantTerm_realUpperBlockDerivative
    (f : FiniteSmoothRationalFunctions F n) (d : FiniteAdelicGL F n)
    (z : InfiniteAdelicGL F a × InfiniteAdelicGL F b) (X : Rect) :
    constantTerm F n h (finiteSmoothEnvelopingAction F n
      (envelopingGenerator F n (complexify F n (upperBlockLieDirection F h X))) f).val
        (AdelicGL.pair F n (blockDiagonalEmbedding h z) d) = 0 := by
  let g : InfiniteAdelicGL F n := blockDiagonalEmbedding h z
  let x := archimedeanGLCoordinates F n g
  let V := realLieAlgebraToMatrix F n (upperBlockLieDirection F h X)
  let S := smoothConstantTermSlice F n h f d
  let p (t : ℝ) : M := x.val * (1 + t • V)
  have hp0 : p 0 = x.val := by simp [p]
  have hp : HasDerivAt p (x.val * V) 0 := by
    have hline : HasDerivAt (fun t : ℝ => (1 : M) + t • V) V 0 := by
      simpa only [one_smul] using ((hasDerivAt_id' (0 : ℝ)).smul_const V).const_add (1 : M)
    exact (ContinuousLinearMap.mul ℝ M x.val).hasFDerivAt.comp_hasDerivAt 0 hline
  have hderiv := ((coordinateExtension_contDiffAt F n S x).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hp hp0.symm
  have hconst (t : ℝ) : coordinateExtension F n S (p t) = S.val g := by
    let u : ArchimedeanGL F n := blockUnipotent h (t • X)
    have hval : p t = (x * u : ArchimedeanGL F n).val := by
      change x.val * (1 + t • V) = x.val * u.val
      rw [show u.val = 1 + t • V from blockUnipotent_smul_val F h X t]
    rw [hval, coordinateExtension_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
    have hu : (archimedeanGLCoordinates F n).symm u =
        blockUnipotent h ((t • X).map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) :=
      map_blockUnipotent (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom h (t • X)
    rw [hu]
    exact constantTerm_pair_mul_blockUnipotent F h f.val d z _
  have hz : fderiv ℝ (coordinateExtension F n S) x.val (x.val * V) = 0 := by
    change HasDerivAt (fun t => coordinateExtension F n S (p t)) _ 0 at hderiv
    rw [funext hconst] at hderiv
    exact hderiv.unique (hasDerivAt_const _ _)
  rw [← smoothDifferential_smoothConstantTermSlice, smoothDifferential_apply]
  exact hz

local instance constantTermRadicalRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance constantTermRadicalContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance constantTermRadicalFiniteAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

omit [CompactSpace (AdeleQuotient F)] in
/-- The complex span of products with an upper radical generator on the left. -/
def upperBlockEnvelopingSpan : Submodule ℂ (EnvelopingAlgebra F n) :=
  Submodule.span ℂ (Set.range fun p : Rect × EnvelopingAlgebra F n =>
    envelopingGenerator F n (complexify F n (upperBlockLieDirection F h p.1)) * p.2)

private def constantTermEvaluation (g : AdelicGL F n) : FiniteSmoothRationalFunctions F n →ₗ[ℂ] ℂ where
  toFun f := constantTerm F n h f.val g
  map_add' f f' := constantTerm_add h f.val f'.val g
  map_smul' c f := constantTerm_smul h c f.val g

/-- Terms in the upper radical span give zero constant-term values at the
infinite Levi and every finite argument. -/
theorem constantTerm_upperBlockEnvelopingSpan
    (f : FiniteSmoothRationalFunctions F n) (d : FiniteAdelicGL F n)
    (z : InfiniteAdelicGL F a × InfiniteAdelicGL F b)
    (u : EnvelopingAlgebra F n) (hu : u ∈ upperBlockEnvelopingSpan F h) :
    constantTerm F n h (finiteSmoothEnvelopingAction F n u f).val
      (AdelicGL.pair F n (blockDiagonalEmbedding h z) d) = 0 := by
  let T : EnvelopingAlgebra F n →ₗ[ℂ] ℂ :=
    (constantTermEvaluation F h (AdelicGL.pair F n (blockDiagonalEmbedding h z) d)).comp
      ((LinearMap.applyₗ (R := ℂ) f).comp (finiteSmoothEnvelopingAction F n).toLinearMap)
  have hT : upperBlockEnvelopingSpan F h ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨X, v⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    change constantTerm F n h
        (finiteSmoothEnvelopingAction F n
          (envelopingGenerator F n (complexify F n (upperBlockLieDirection F h X)) * v) f).val
        (AdelicGL.pair F n (blockDiagonalEmbedding h z) d) = 0
    rw [map_mul, Module.End.mul_apply]
    exact constantTerm_realUpperBlockDerivative F h _ d z X
  exact LinearMap.mem_ker.mp (hT hu)

end Langlands.Automorphic
