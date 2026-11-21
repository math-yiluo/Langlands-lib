import Langlands.Global.AdelicBlockCoefficientSmoothness
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiation of realized adelic Levi coefficients

The first variation of a normalized section's Levi coefficient is a sum of
actual block Lie derivatives. The diagonal-block projection of the mixed
matrix tangent gives the direction in each block.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 85000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear NumberField
open AdelicBlockParabolic AdelicBlockDeterminantCharacter
open ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local instance (t : ℕ) : AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance {t : ℕ} (U : OperatorRealization F t) : AddCommGroup U.Space :=
  Submodule.addCommGroup _

local notation "A" => ArchimedeanMatrix F n
local notation "W" => coefficientValues F B S
local notation "D" => archimedeanDiagonalBlock F B

/-- The mixed-coordinate matrix of the infinite block diagonal component of a Levi point. -/
abbrev infiniteLeviMatrix (m : FullLevi F B) : A :=
  (archimedeanGLCoordinates F n
    (B.leviEmbedding (InfiniteAdeles F) (leviInfinite F B m))).val

private theorem diagonalBlock_levi_mul (m : InfiniteLevi F B) (x : A) (i : Fin B.length) :
    D i ((archimedeanGLCoordinates F n (B.leviEmbedding (InfiniteAdeles F) m)).val * x) =
      (archimedeanGLCoordinates F (B.size i) (m i)).val * D i x := by
  apply Matrix.ext
  intro a b
  change ((archimedeanGLCoordinates F n (B.leviEmbedding (InfiniteAdeles F) m)).val * x)
    (B.index i a) (B.index i b) = _
  rw [Matrix.mul_apply, ← B.indexEquiv.sum_comp, Fintype.sum_sigma, Fintype.sum_eq_single i]
  · rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c _
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (B.leviEmbedding (InfiniteAdeles F) m (B.index i a) (B.index i c))) *
      x (B.index i c) (B.index i b) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (m i a c)) * x (B.index i c) (B.index i b)
    rw [B.leviEmbedding_apply_same]
  · intro j hji
    apply Finset.sum_eq_zero
    intro c _
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (B.leviEmbedding (InfiniteAdeles F) m (B.index i a) (B.index j c)) *
        x (B.index j c) (B.index i b) = 0
    rw [B.leviEmbedding_apply_ne _ m a c hji.symm, map_zero, zero_mul]

private theorem diagonalBlock_one (i : Fin B.length) : D i 1 = 1 := by
  apply Matrix.ext
  intro a b
  change (1 : A) (B.index i a) (B.index i b) = (1 : ArchimedeanMatrix F (B.size i)) a b
  simp [Matrix.one_apply, (B.index i).injective.eq_iff]

private abbrev blockDirection (i : Fin B.length) (X : A) :=
  (ArchimedeanGL.realLieAlgebraToMatrix F (B.size i)).symm (D i X)

private def blockOperator (i : Fin B.length) (X : A) : Module.End ℂ (S i).Space :=
  (S i).envelopingAction (ArchimedeanGL.envelopingGenerator F (B.size i)
    (ArchimedeanGL.complexify F (B.size i) (blockDirection F B i X)))

/-- Apply the projected real Lie generator to each tensor slot in turn and sum. -/
def coefficientDifferential (X : A) : Module.End ℂ W :=
  (coefficientEquiv F B S).toLinearMap.comp
    ((∑ i, (PiTensorProduct.map (fun j =>
      if j = i then blockOperator F B S j X else LinearMap.id) :
        Module.End ℂ (⨂[ℂ] j, (S j).Space))).comp
      (coefficientEquiv F B S).symm.toLinearMap)

private abbrev blockValue (i : Fin B.length) (v : (S i).Space) (m : FullLevi F B) : ℂ :=
  evaluate F (B.size i) ((S i).toContinuous v) (m i)

private theorem coefficientDifferential_tprod_apply (X : A) (v : ∀ i, (S i).Space)
    (m : FullLevi F B) :
    (coefficientDifferential F B S X (coefficientEquiv F B S (PiTensorProduct.tprod ℂ v))).val m =
      ∑ i, (∏ j ∈ Finset.univ.erase i, blockValue F B S j (v j) m) *
        blockValue F B S i (blockOperator F B S i X (v i)) m := by
  simp only [coefficientDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.sum_apply, map_sum, Submodule.coe_sum,
    Finset.sum_apply, PiTensorProduct.map_tprod, coefficientEquiv_tprod_apply, blockCoefficient]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.prod_erase_mul _ _ hi]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp only [ite_eq_right (Finset.ne_of_mem_erase hj), LinearMap.id_apply]
  · simp

private abbrev blockSlice (d : FiniteLevi F B) (i : Fin B.length) (v : (S i).Space) :
    ArchimedeanMatrix F (B.size i) → ℂ :=
  ArchimedeanGL.coordinateExtension F (B.size i)
    (finiteSmoothSlice F (B.size i) (d i) ((S i).ambient v))

private theorem coefficientExtension_tprod_apply (d : FiniteLevi F B) (v : ∀ i, (S i).Space)
    (x : A) :
    coefficientExtension F B S d (coefficientEquiv F B S (PiTensorProduct.tprod ℂ v)) x =
      ∏ i, blockSlice F B S d i (v i) (D i x) := by
  simp only [coefficientExtension, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  change indexedEvaluation _ (PiTensorProduct.tprod ℂ v) (fun i => D i x) = _
  rw [indexedEvaluation_tprod]
  rfl

/-- The extended evaluation after left multiplication by a fixed Levi matrix agrees
with coefficient evaluation at the Levi point translated by the parabolic projection. -/
theorem coefficientExtension_levi_mul_parabolic (m : FullLevi F B) (c : W)
    (a : Infinite F B) :
    coefficientExtension F B S (leviFinite F B m) c
      (infiniteLeviMatrix F B m * (archimedeanGLCoordinates F n a.val).val) =
      c.val (m * leviPair F B (B.leviProjection (InfiniteAdeles F) a) 1) := by
  let p : Infinite F B := B.leviInParabolic (InfiniteAdeles F) (leviInfinite F B m)
  have h : (archimedeanGLCoordinates F n (p * a).val).val =
      infiniteLeviMatrix F B m * (archimedeanGLCoordinates F n a.val).val := by
    change (archimedeanGLCoordinates F n (p.val * a.val)).val = _
    rw [map_mul, Units.val_mul]
    rfl
  rw [← h, coefficientExtension_apply_parabolic, map_mul]
  change c.val (leviPair F B (B.leviProjection (InfiniteAdeles F)
    (B.leviInParabolic (InfiniteAdeles F) (leviInfinite F B m)) *
      B.leviProjection (InfiniteAdeles F) a) (leviFinite F B m)) = _
  rw [B.leviProjection_section]
  apply congrArg c.val
  funext i
  change AdelicGL.pair F (B.size i) _ _ =
    m i * AdelicGL.pair F (B.size i) (B.leviProjection (InfiniteAdeles F) a i) 1
  rw [← AdelicGL.pair_projections F (B.size i) (m i), AdelicGL.pair_mul]
  rw [mul_one]
  rfl

private theorem blockSlice_value (m : FullLevi F B) (i : Fin B.length) (v : (S i).Space) :
    blockSlice F B S (leviFinite F B m) i v
      (archimedeanGLCoordinates F (B.size i) (leviInfinite F B m i)).val =
      blockValue F B S i v m := by
  simp only [blockSlice, ArchimedeanGL.coordinateExtension_apply,
    ContinuousMulEquiv.symm_apply_apply, finiteSmoothSlice_apply,
    OperatorRealization.evaluate_toContinuous]
  exact congrArg (evaluate F (B.size i) ((S i).ambient v).val)
    (AdelicGL.pair_projections F (B.size i) (m i))

private theorem blockSlice_hasDerivAt (m : FullLevi F B) (i : Fin B.length) (v : (S i).Space)
    {b : ℝ → A} (hb₀ : b 0 = 1) {X : A} (hb : HasDerivAt b X 0) :
    HasDerivAt (fun t => blockSlice F B S (leviFinite F B m) i v
      ((archimedeanGLCoordinates F (B.size i) (leviInfinite F B m i)).val * D i (b t)))
      (blockValue F B S i (blockOperator F B S i X v) m) 0 := by
  let a := leviInfinite F B m i
  let d := leviFinite F B m i
  let g := archimedeanGLCoordinates F (B.size i) a
  let s := finiteSmoothSlice F (B.size i) d ((S i).ambient v)
  have hD : HasDerivAt (fun t => D i (b t)) (D i X) 0 :=
    (D i).hasFDerivAt.comp_hasDerivAt 0 hb
  have hcurve := hD.const_mul g.val
  have hbase : g.val = g.val * D i (b 0) := by
    rw [hb₀, diagonalBlock_one, mul_one]
  have hd := (ArchimedeanGL.coordinateExtension_contDiffAt F (B.size i) s g).differentiableAt
    (by simp)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve hbase
  have he := evaluate_finiteSmoothEnvelopingAction_real_generator F (B.size i)
    (blockDirection F B i X) ((S i).ambient v) a d
  change evaluate F (B.size i) _ (AdelicGL.pair F (B.size i) a d) =
    fderiv ℝ (ArchimedeanGL.coordinateExtension F (B.size i) s) g.val
      (g.val * ArchimedeanGL.realLieAlgebraToMatrix F (B.size i) (blockDirection F B i X)) at he
  rw [(ArchimedeanGL.realLieAlgebraToMatrix F (B.size i)).apply_symm_apply] at he
  have hpair : AdelicGL.pair F (B.size i) a d = m i := AdelicGL.pair_projections F _ _
  rw [hpair, ← (S i).ambient_envelopingAction, ← (S i).evaluate_toContinuous] at he
  change blockValue F B S i (blockOperator F B S i X v) m = _ at he
  rw [he]
  exact hcomp

private theorem coefficientExtension_hasDerivAt_tprod (m : FullLevi F B) (v : ∀ i, (S i).Space)
    {b : ℝ → A} (hb₀ : b 0 = 1) {X : A} (hb : HasDerivAt b X 0) :
    HasDerivAt (fun t => coefficientExtension F B S (leviFinite F B m)
      (coefficientEquiv F B S (PiTensorProduct.tprod ℂ v)) (infiniteLeviMatrix F B m * b t))
      ((coefficientDifferential F B S X (coefficientEquiv F B S (PiTensorProduct.tprod ℂ v))).val
        m) 0 := by
  simp only [coefficientExtension_tprod_apply, infiniteLeviMatrix, diagonalBlock_levi_mul,
    coefficientDifferential_tprod_apply]
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => blockSlice_hasDerivAt F B S m i (v i) hb₀ hb)
  simpa only [hb₀, diagonalBlock_one, mul_one, blockSlice_value, smul_eq_mul] using h

/-- Along a curve based at the identity, the derivative of the ambient
coefficient evaluated after a fixed Levi multiplication is the actual sum of
block Lie derivatives evaluated at that Levi point. -/
theorem coefficientExtension_hasDerivAt (m : FullLevi F B) (c : W)
    {b : ℝ → A} (hb₀ : b 0 = 1) {X : A} (hb : HasDerivAt b X 0) :
    HasDerivAt (fun t => coefficientExtension F B S (leviFinite F B m) c
      (infiniteLeviMatrix F B m * b t)) ((coefficientDifferential F B S X c).val m) 0 := by
  obtain ⟨v, rfl⟩ := (coefficientEquiv F B S).surjective c
  induction v using PiTensorProduct.induction_on with
  | smul_tprod z v =>
    have h := coefficientExtension_hasDerivAt_tprod F B S m v hb₀ hb
    simpa only [map_smul, Submodule.coe_smul, Pi.smul_apply] using! h.const_smul z
  | add v w hv hw =>
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using! hv.add hw

end Langlands.Global.AdelicBlockScalarSections
