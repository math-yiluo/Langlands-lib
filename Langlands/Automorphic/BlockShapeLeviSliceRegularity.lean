import Langlands.Automorphic.BlockShapeSingleCut
import Langlands.Automorphic.GeneralLinearBlockConstantTermSmooth

/-! # Smoothness and growth of the individual Levi slices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MeasureTheory Set Topology
open scoped Classical ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global Langlands.Global.ArchimedeanGL
  Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints GeneralLinearBlockSemidirect
open scoped CategoryTheory.MonObj

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "R(" e ")" => adelicPoints F G (blockUnipotent (Fin n) RF e)

local instance leviSliceRegularityAffine : IsAffine (G).X.left := isAffine_groupScheme (Fin n) RF
local instance leviSliceRegularitySmooth : Smooth (G).X.hom := smoothStatement (Fin n) RF
local instance leviSliceRegularityLocallyCompact (e : Fin n → ℤ) : LocallyCompactSpace R(e) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace
local instance leviSliceRegularityRationalAddCommGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance leviSliceRegularityContinuousAddCommGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance leviSliceRegularityFiniteAddCommGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _

private theorem exists_uniform_polynomialGrowth (f : FiniteSmoothRationalFunctions F n)
    (hf : HasPolynomialGrowth F n f.val) {K : Set (FiniteAdelicGL F n)} (hK : IsCompact K) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∃ d : ℕ, ∀ b ∈ K, ∀ a : InfiniteAdelicGL F n,
      ‖ContinuousRationalFunctions.evaluate F n f.val (AdelicGL.pair F n a b)‖ ≤
        C * matrixHeight F n a ^ d := by
  obtain ⟨L, hL⟩ := f.property.2
  let T := FiniteAdelicGL F n ⧸ L.toSubgroup
  let : DiscreteTopology T := QuotientGroup.discreteTopology L.isOpen
  let p : FiniteAdelicGL F n → T := QuotientGroup.mk
  let hP := (hK.image (show Continuous p from QuotientGroup.continuous_mk)).finite_of_discrete
  let P := hP.toFinset
  choose C hC d hd using fun q : T => hf q.out
  refine ⟨∑ q ∈ P, C q, Finset.sum_nonneg (fun q _ => hC q), P.sup d, ?_⟩
  intro b hb a
  let q := p b
  have hq : q ∈ P := hP.mem_toFinset.mpr ⟨b, hb, rfl⟩
  have hbq : q.out⁻¹ * b ∈ L.toSubgroup := QuotientGroup.eq.mp (Quotient.out_eq q)
  let l : L := ⟨_, hbq⟩
  have heval := congrArg (fun f : ContinuousRationalFunctions F n =>
    ContinuousRationalFunctions.evaluate F n f (AdelicGL.pair F n a q.out)) (hL l)
  change f.val.val.val (AdelicGL.pair F n a q.out * AdelicGL.ofFinite F n l.val) =
    f.val.val.val (AdelicGL.pair F n a q.out) at heval
  rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one] at heval
  change f.val.val.val (AdelicGL.pair F n a (q.out * (q.out⁻¹ * b))) = _ at heval
  rw [mul_inv_cancel_left] at heval
  change ‖f.val.val.val (AdelicGL.pair F n a b)‖ ≤ _
  rw [heval]
  exact (hd q a).trans (mul_le_mul
    (Finset.single_le_sum (f := C) (fun j _ => hC j) hq)
    (pow_le_pow_right₀ (one_le_matrixHeight F n a) (Finset.le_sup hq))
    (pow_nonneg (matrixHeight_nonneg F n a) _) (Finset.sum_nonneg fun j _ => hC j))

/-- Each archimedean slice of the normalized block term has polynomial
growth when the source form has polynomial growth. -/
theorem finiteSmoothBlockConstantTerm_polynomialGrowth (e : Fin n → ℤ)
    (f : FiniteSmoothRationalFunctions F n) (hf : HasPolynomialGrowth F n f.val)
    (b : FiniteAdelicGL F n) :
    ArchimedeanGL.HasPolynomialGrowth F n
      (fun a => finiteSmoothBlockConstantTerm F e f ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (AdelicGL.pair F n a b))) := by
  obtain ⟨D, _, hDc, hD⟩ := exists_blockConstantTerm_compactDomain F e
  let yFull (y : R(e)) := GeneralLinearGroupPoints.adelicHomeomorph F n y.val
  let yInf (y : R(e)) := AdelicGL.infinite F n (yFull y)
  let yFin (y : R(e)) := AdelicGL.finite F n (yFull y) * b
  let K := yFin '' closure D
  have hFull : Continuous yFull := (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp
    continuous_subtype_val
  have hInf : Continuous yInf := (AdelicGL.infinite F n).continuous.comp hFull
  have hK : IsCompact K := hDc.image (((AdelicGL.finite F n).continuous.comp hFull).mul_const b)
  obtain ⟨C, hC, d, hd⟩ := exists_uniform_polynomialGrowth F f hf hK
  obtain ⟨A, hA⟩ := hDc.exists_bound_of_continuousOn
    ((continuous_matrixHeight F n).comp hInf).continuousOn
  let M := max 1 A
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  refine ⟨C * M ^ d, mul_nonneg hC (pow_nonneg hM _), d, fun a => ?_⟩
  let mass := (Measure.haar : Measure R(e)) D
  let bound := C * M ^ d * matrixHeight F n a ^ d
  have hmass : mass < ⊤ :=
    (measure_mono (subset_closure : D ⊆ closure D)).trans_lt hDc.measure_lt_top
  have hbound (y : R(e)) (hy : y ∈ D) :
      ‖ContinuousRationalFunctions.evaluate F n f.val
        (yFull y * AdelicGL.pair F n a b)‖ ≤ bound := by
    have hy' : y ∈ closure D := subset_closure hy
    have hval : yFull y * AdelicGL.pair F n a b = AdelicGL.pair F n (yInf y * a) (yFin y) := by
      conv_lhs => rw [← AdelicGL.pair_projections F n (yFull y)]
      exact AdelicGL.pair_mul F n _ _ _ _
    have hyM : matrixHeight F n (yInf y) ≤ M :=
      ((le_abs_self _).trans (by simpa only [Function.comp_apply, Real.norm_eq_abs] using hA y hy')).trans
        (le_max_right _ _)
    have hheight := (matrixHeight_mul_le F n (yInf y) a).trans
      (mul_le_mul_of_nonneg_right hyM (matrixHeight_nonneg F n a))
    rw [hval]
    calc
      _ ≤ C * matrixHeight F n (yInf y * a) ^ d := hd _ ⟨y, hy', rfl⟩ _
      _ ≤ C * (M * matrixHeight F n a) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (matrixHeight_nonneg F n _) hheight d) hC
      _ = bound := by simp only [bound, mul_pow, mul_assoc]
  change ‖finiteSmoothBlockConstantTerm F e f ((GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.pair F n a b))‖ ≤ bound
  rw [hD, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  have hI := norm_setIntegral_le_of_norm_le_const hmass hbound
  refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans ?_
  change mass.toReal⁻¹ * (bound * mass.toReal) ≤ bound
  by_cases hzero : mass.toReal = 0
  · simp only [hzero, inv_zero, zero_mul]
    exact mul_nonneg (mul_nonneg hC (pow_nonneg hM _))
      (pow_nonneg (matrixHeight_nonneg F n a) _)
  · rw [mul_left_comm, inv_mul_cancel₀ hzero, mul_one]

variable (B : BlockShape n) (i : Fin B.length)

private theorem singleBlock_map {A C : Type u} [CommRing A] [CommRing C] (h : A →+* C)
    (x : GeneralLinear (B.size i) A) :
    Matrix.GeneralLinearGroup.map h (blockShapeSingleEmbedding B A i x) =
      blockShapeSingleEmbedding B C i (Matrix.GeneralLinearGroup.map h x) := by
  apply Units.ext
  ext p q
  obtain ⟨j, a, rfl⟩ := exists_eq_index B p
  obtain ⟨k, b, rfl⟩ := exists_eq_index B q
  change h (B.leviEmbedding A (Pi.mulSingle i x) (B.index j a) (B.index k b)) =
    B.leviEmbedding C (Pi.mulSingle i (Matrix.GeneralLinearGroup.map h x))
      (B.index j a) (B.index k b)
  by_cases hjk : j = k
  · subst k
    rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same]
    by_cases hj : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Matrix.GeneralLinearGroup.map_apply]
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
      exact congrArg (fun y : GeneralLinear (B.size j) C => y a b)
        (map_one (Matrix.GeneralLinearGroup.map h))
  · rw [B.leviEmbedding_apply_ne A _ a b hjk, B.leviEmbedding_apply_ne C _ a b hjk, map_zero]

private theorem singleBlock_pair (a : InfiniteAdelicGL F (B.size i))
    (b : FiniteAdelicGL F (B.size i)) :
    blockShapeSingleEmbedding B (Adeles F) i (AdelicGL.pair F (B.size i) a b) =
      AdelicGL.pair F n (blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a)
        (blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i b) := by
  let x := AdelicGL.pair F (B.size i) a b
  have hInf : AdelicGL.infinite F n (blockShapeSingleEmbedding B (Adeles F) i x) =
      blockShapeSingleEmbedding B (InfiniteAdeleRing F) i (AdelicGL.infinite F (B.size i) x) :=
    singleBlock_map B i (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x
  have hFin : AdelicGL.finite F n (blockShapeSingleEmbedding B (Adeles F) i x) =
      blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i (AdelicGL.finite F (B.size i) x) :=
    singleBlock_map B i (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x
  apply AdelicGL.ext_infinite_finite F n
  · rw [hInf]
    simp only [x, AdelicGL.infinite_pair]
  · rw [hFin]
    simp only [x, AdelicGL.finite_pair]

private def sliceRightArgument (m : AdelicBlockParabolic.FullLevi F B)
    (g : AdelicGL F n) : AdelicGL F n :=
  B.leviEmbedding (Adeles F) (Function.update m i 1) * g

private theorem blockShapeLeviSliceFactor_pair
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B)
    (a : InfiniteAdelicGL F (B.size i)) (b : FiniteAdelicGL F (B.size i)) :
    ContinuousRationalFunctions.evaluate F (B.size i) (blockShapeLeviSliceFactor B F f g m i)
        (AdelicGL.pair F (B.size i) a b) =
      blockShapeConstantTerm B F f (AdelicGL.pair F n
        (blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a *
          AdelicGL.infinite F n (sliceRightArgument F B i m g))
        (blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i b *
          AdelicGL.finite F n (sliceRightArgument F B i m g))) := by
  let x := AdelicGL.pair F (B.size i) a b
  have hx : Function.update m i x = Pi.mulSingle i x * Function.update m i 1 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
    · simp only [Function.update_of_ne hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]
  change blockShapeConstantTerm B F f (B.leviEmbedding (Adeles F) (Function.update m i x) * g) = _
  rw [hx, map_mul, mul_assoc]
  change blockShapeConstantTerm B F f
    (blockShapeSingleEmbedding B (Adeles F) i x * sliceRightArgument F B i m g) = _
  rw [singleBlock_pair F B i a b, AdelicGL.pair_mul_right]

/-- The real matrix inclusion of one block, with zero on the other blocks. -/
def archimedeanBlockMatrixInclusion :
    ArchimedeanMatrix F (B.size i) →ₗ[ℝ] ArchimedeanMatrix F n :=
  (Matrix.reindexLinearEquiv ℝ (mixedEmbedding.mixedSpace F) B.indexEquiv B.indexEquiv).toLinearMap ∘ₗ
    ({ toFun := Matrix.blockDiagonal'
       map_add' := Matrix.blockDiagonal'_add
       map_smul' := Matrix.blockDiagonal'_smul } :
      (∀ j, ArchimedeanMatrix F (B.size j)) →ₗ[ℝ] Matrix B.Index B.Index (mixedEmbedding.mixedSpace F)) ∘ₗ
    LinearMap.single ℝ (fun j => ArchimedeanMatrix F (B.size j)) i

omit [NumberField F] in
private theorem archimedeanBlockMatrixInclusion_same (X : ArchimedeanMatrix F (B.size i))
    (j : Fin B.length) (a b : Fin (B.size j)) :
    archimedeanBlockMatrixInclusion F B i X (B.index j a) (B.index j b) =
      (Pi.single i X : ∀ j, ArchimedeanMatrix F (B.size j)) j a b := by
  change Matrix.blockDiagonal' (Pi.single i X)
    (B.indexEquiv.symm (B.indexEquiv ⟨j, a⟩))
    (B.indexEquiv.symm (B.indexEquiv ⟨j, b⟩)) = _
  simp only [Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]

omit [NumberField F] in
private theorem archimedeanBlockMatrixInclusion_ne (X : ArchimedeanMatrix F (B.size i))
    {j k : Fin B.length} (a : Fin (B.size j)) (b : Fin (B.size k)) (hjk : j ≠ k) :
    archimedeanBlockMatrixInclusion F B i X (B.index j a) (B.index k b) = 0 := by
  change Matrix.blockDiagonal' (Pi.single i X)
    (B.indexEquiv.symm (B.indexEquiv ⟨j, a⟩))
    (B.indexEquiv.symm (B.indexEquiv ⟨k, b⟩)) = _
  simp only [Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hjk]

omit [NumberField F] in
private theorem archimedeanSingleBlock_val (a : ArchimedeanGL F (B.size i)) :
    (blockShapeSingleEmbedding B (mixedEmbedding.mixedSpace F) i a).val =
      archimedeanBlockMatrixInclusion F B i a.val +
        (1 - archimedeanBlockMatrixInclusion F B i 1) := by
  let j := blockShapeSingleEmbedding B (mixedEmbedding.mixedSpace F) i
  let L := archimedeanBlockMatrixInclusion F B i
  have hd : (j a).val - (j 1).val = L (a.val - 1) := by
    apply Matrix.ext
    intro p q
    obtain ⟨k, x, rfl⟩ := exists_eq_index B p
    obtain ⟨l, y, rfl⟩ := exists_eq_index B q
    change B.leviEmbedding _ (Pi.mulSingle i a) (B.index k x) (B.index l y) -
      B.leviEmbedding _ (Pi.mulSingle i (1 : ArchimedeanGL F (B.size i))) (B.index k x) (B.index l y) =
      L (a.val - 1) (B.index k x) (B.index l y)
    by_cases hkl : k = l
    · subst l
      rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same, archimedeanBlockMatrixInclusion_same]
      by_cases hk : k = i
      · subst k
        simp only [Pi.mulSingle_eq_same, Pi.single_eq_same, Matrix.sub_apply, Units.val_one]
      · simp only [Pi.mulSingle_eq_of_ne hk, Pi.single_eq_of_ne hk, Matrix.zero_apply, sub_self]
    · rw [B.leviEmbedding_apply_ne _ _ _ _ hkl, B.leviEmbedding_apply_ne _ _ _ _ hkl,
        archimedeanBlockMatrixInclusion_ne F B i _ _ _ hkl, sub_zero]
  rw [map_one, Units.val_one, map_sub] at hd
  change (j a).val = _
  rw [sub_eq_sub_iff_add_eq_add] at hd
  rw [← add_sub_assoc, ← hd, add_sub_cancel_right]

omit [NumberField F] in
private theorem infiniteBlock_coordinates (a : InfiniteAdelicGL F (B.size i)) :
    archimedeanGLCoordinates F n (blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a) =
      blockShapeSingleEmbedding B (mixedEmbedding.mixedSpace F) i
        (archimedeanGLCoordinates F (B.size i) a) :=
  singleBlock_map B i (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom a

set_option maxHeartbeats 800000 in
/-- Each individual Levi slice is an original finite-smooth rational-invariant
function. -/
def blockShapeFiniteSmoothLeviSliceFactor
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) : FiniteSmoothRationalFunctions F (B.size i) := by
  refine ⟨blockShapeLeviSliceFactor B F f g m i, ?_,
    blockShapeLeviSliceFactor_mem_finiteSmoothSubrepresentation B F f g m i⟩
  change _ ∈ (infiniteSmoothSubrepresentation F (B.size i)).toSubmodule
  simp only [infiniteSmoothSubrepresentation, Submodule.mem_iInf, Submodule.mem_comap]
  intro b
  let c := sliceRightArgument F B i m g
  let d := blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i b * AdelicGL.finite F n c
  let L := archimedeanBlockMatrixInclusion F B i
  let A (x : ArchimedeanMatrix F (B.size i)) :=
    (L x + (1 - L 1)) * (archimedeanGLCoordinates F n (AdelicGL.infinite F n c)).val
  let a (x : ArchimedeanGL F (B.size i)) :=
    blockShapeSingleEmbedding B (InfiniteAdeleRing F) i
      ((archimedeanGLCoordinates F (B.size i)).symm x) * AdelicGL.infinite F n c
  have hA : ContDiff ℝ ∞ A :=
    (L.toContinuousLinearMap.contDiff.add contDiff_const).mul contDiff_const
  have hval (x : ArchimedeanGL F (B.size i)) :
      A x.val = (archimedeanGLCoordinates F n (a x)).val := by
    simp only [a, map_mul, infiniteBlock_coordinates, ContinuousMulEquiv.apply_symm_apply,
      Units.val_mul, archimedeanSingleBlock_val]
    rfl
  let U := range (Units.val : ArchimedeanGL F (B.size i) → ArchimedeanMatrix F (B.size i))
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hdiff : ContDiffOn ℝ ∞
      (blockConstantTermMatrixSlice F (standardBlockWeight B.cuts) f d ∘ A) U :=
    (contDiffOn_blockConstantTermMatrixSlice F _ f d).comp hA.contDiffOn (by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, (hval x).symm⟩)
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F (B.size i)) 𝓘(ℝ, ℂ) ∞ _
  have heval : (fun x : ArchimedeanGL F (B.size i) =>
      infiniteSlice F (B.size i) b (blockShapeLeviSliceFactor B F f g m i)
        ((archimedeanGLCoordinates F (B.size i)).symm x)) =
      (fun x : ArchimedeanGL F (B.size i) =>
        blockConstantTermMatrixSlice F (standardBlockWeight B.cuts) f d (A x.val)) := by
    funext x
    change ContinuousRationalFunctions.evaluate F _ (blockShapeLeviSliceFactor B F f g m i)
      (AdelicGL.pair F _ ((archimedeanGLCoordinates F _).symm x) b) = _
    rw [blockShapeLeviSliceFactor_pair F B i, hval, blockConstantTermMatrixSlice]
    have hc : (unitsChart F n).symm (archimedeanGLCoordinates F n (a x)).val =
        archimedeanGLCoordinates F n (a x) := by
      simp only [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
    rw [hc, ContinuousMulEquiv.symm_apply_apply]
    rfl
  rw [heval]
  intro x
  exact (hdiff.contDiffAt (hU.mem_nhds ⟨x, rfl⟩)).comp_contMDiffAt
    (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) x)

private theorem exists_matrixHeight_singleBlock_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : InfiniteAdelicGL F (B.size i),
      matrixHeight F n (blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a) ≤
        C * matrixHeight F (B.size i) a := by
  let j := blockShapeSingleEmbedding B (InfiniteAdeleRing F) i
  let L := (archimedeanBlockMatrixInclusion F B i).toContinuousLinearMap
  let z := 1 - L 1
  let C := max 1 (‖L‖ + ‖z‖)
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C, hC, fun a => ?_⟩
  have hval (a : InfiniteAdelicGL F (B.size i)) :
      ‖(archimedeanGLCoordinates F n (j a)).val‖ ≤ C * matrixHeight F (B.size i) a := by
    rw [show archimedeanGLCoordinates F n (j a) =
      blockShapeSingleEmbedding B (mixedEmbedding.mixedSpace F) i
        (archimedeanGLCoordinates F (B.size i) a) from infiniteBlock_coordinates F B i a,
      archimedeanSingleBlock_val F B i]
    let x := (archimedeanGLCoordinates F (B.size i) a).val
    change ‖L x + z‖ ≤ C * matrixHeight F (B.size i) a
    calc
      ‖L x + z‖ ≤ ‖L x‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖L‖ * matrixHeight F (B.size i) a + ‖z‖ * matrixHeight F (B.size i) a :=
        add_le_add ((L.le_opNorm x).trans (mul_le_mul_of_nonneg_left
          (norm_val_le_matrixHeight F (B.size i) a) (norm_nonneg _)))
          (le_mul_of_one_le_right (norm_nonneg _) (one_le_matrixHeight F (B.size i) a))
      _ ≤ C * matrixHeight F (B.size i) a := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (matrixHeight_nonneg F (B.size i) a)
  have hinv := hval a⁻¹
  rw [map_inv, map_inv, matrixHeight_inv] at hinv
  change matrixHeight F n (j a) ≤ _
  exact max_le
    (one_le_mul_of_one_le_of_one_le hC (one_le_matrixHeight F (B.size i) a))
    (max_le (hval a) hinv)

/-- The individual Levi slices inherit polynomial growth on each finite
adelic slice. -/
theorem blockShapeLeviSliceFactor_hasPolynomialGrowth
    (f : FiniteSmoothRationalFunctions F n) (hf : HasPolynomialGrowth F n f.val)
    (g : AdelicGL F n) (m : AdelicBlockParabolic.FullLevi F B) :
    HasPolynomialGrowth F (B.size i) (blockShapeLeviSliceFactor B F f g m i) := by
  intro b
  let c := sliceRightArgument F B i m g
  let d := blockShapeSingleEmbedding B (FiniteAdeleRing (𝓞 F) F) i b * AdelicGL.finite F n c
  let h := AdelicGL.infinite F n c
  obtain ⟨C, hC, e, he⟩ := finiteSmoothBlockConstantTerm_polynomialGrowth F
    (standardBlockWeight B.cuts) f hf d
  obtain ⟨D, hD, hDb⟩ := exists_matrixHeight_singleBlock_le F B i
  let M := D * matrixHeight F n h
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans hD) (matrixHeight_nonneg F n h)
  refine ⟨C * M ^ e, mul_nonneg hC (pow_nonneg hM e), e, fun a => ?_⟩
  let x := blockShapeSingleEmbedding B (InfiniteAdeleRing F) i a
  have hheight : matrixHeight F n (x * h) ≤ M * matrixHeight F (B.size i) a := by
    calc
      _ ≤ matrixHeight F n x * matrixHeight F n h := matrixHeight_mul_le F n x h
      _ ≤ (D * matrixHeight F (B.size i) a) * matrixHeight F n h :=
        mul_le_mul_of_nonneg_right (hDb a) (matrixHeight_nonneg F n h)
      _ = _ := mul_right_comm _ _ _
  change ‖ContinuousRationalFunctions.evaluate F _ (blockShapeLeviSliceFactor B F f g m i)
    (AdelicGL.pair F _ a b)‖ ≤ _
  rw [blockShapeLeviSliceFactor_pair F B i]
  calc
    _ ≤ C * matrixHeight F n (x * h) ^ e := he (x * h)
    _ ≤ C * (M * matrixHeight F (B.size i) a) ^ e :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (matrixHeight_nonneg F n _) hheight e) hC
    _ = _ := by rw [mul_pow, mul_assoc]

end Langlands.Automorphic
