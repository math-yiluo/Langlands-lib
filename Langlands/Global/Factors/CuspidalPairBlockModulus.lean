import Langlands.Global.Factors.CuspidalPairLeviCoordinates
import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveProof
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint

/-! # The parabolic modulus at scalar points of a two-block Levi -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 120000

open CategoryTheory AlgebraicGeometry NumberField Opposite TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear Langlands.GroupScheme.Dynamic
open AdelicGroupPoints AdelicBlockEisensteinGeometry AdelicBlockDeterminantCharacter

variable (F : Type) [Field F] [NumberField F] (r t : ℕ)

local notation "B" => blockShape r t
local notation "N" => (r + t + 2)
local notation "𝕜" => CommRingCat.of F
local notation "GLG" => groupScheme (Fin N) 𝕜
local notation "i₀" => firstBlock r t
local notation "i₁" => secondBlock r t
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin N) 𝕜 wt
local notation "U" => blockUnipotentScheme (Fin N) 𝕜 wt
local notation "M" => blockLeviScheme (Fin N) 𝕜 wt
local notation "p" => blockParabolicHom (Fin N) 𝕜 wt
local notation "mG" => blockLeviHom (Fin N) 𝕜 wt
local notation "uG" => blockUnipotentHom (Fin N) 𝕜 wt
local notation "l" => blockLeviInclusion F B
local notation "hP" => isRepresentedBy_parabolic_diagonalCocharacter (Fin N) 𝕜 wt
local notation "hM" => isRepresentedBy_centralizer_diagonalCocharacter (Fin N) 𝕜 wt
local notation "hU" => isRepresentedBy_unipotent_diagonalCocharacter (Fin N) 𝕜 wt

local instance blockModulusGLAffineHom : IsAffineHom (GLG).X.hom := isAffineHom_groupScheme _ _
local instance blockModulusGLSeparated : IsSeparated (GLG).X.hom := inferInstance
local instance blockModulusGLFiniteType : LocallyOfFiniteType (GLG).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin N)).smooth
  inferInstance
local instance blockModulusUnipotentAffineHom : IsAffineHom (U).X.hom := (isClosedSubgroup_blockUnipotentHom (Fin N) 𝕜 wt).isAffineHom
local instance blockModulusUnipotentAffine : IsAffine (U).X.left := isAffine_of_isAffineHom (U).X.hom
local instance blockModulusParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance blockModulusParabolicFiniteType : LocallyOfFiniteType (P).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType (isClosedSubgroup_blockParabolicHom (Fin N) 𝕜 wt)
local instance blockModulusLeviAffine : IsAffine (M).X.left :=
  have := (blockLevi_isConnectedReductive F B).isAffineHom
  isAffine_of_isAffineHom (M).X.hom
local instance blockModulusLeviFiniteType : LocallyOfFiniteType (M).X.hom :=
  have := (blockLevi_isConnectedReductive F B).smooth
  inferInstance
local instance blockModulusUnipotentFiniteType : LocallyOfFiniteType (U).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType (isClosedSubgroup_blockUnipotentHom (Fin N) 𝕜 wt)
local instance blockModulusUnipotentMono : Mono (uG).hom.hom := (hU).1

section Coordinates

variable (A : Type) [CommRing A] [Algebra F A]

local notation "DU" => Additive (lieKernel U A)
local notation "Mat" => Matrix (Fin N) (Fin N) A
local notation "Sε" => CommAlgCat.of F (DualNumber A)

/-- Strictly upper block entries, using the weights of the block cocharacter. -/
private abbrev UpperEntries := {ij : Fin N × Fin N // wt ij.2 < wt ij.1}

private def radicalTangentMatrix : DU →ₗ[A] Mat :=
  (GeneralLinear.DualNumber.pointKernelLinearEquiv (R := 𝕜) (A := A)).symm.toLinearMap.comp
    (Lie.targetMapLinear uG A)

omit [NumberField F] in
private theorem radicalTangentMatrix_injective : Function.Injective (radicalTangentMatrix F r t A) :=
  fun x y h => by
    let e := GeneralLinear.DualNumber.pointKernelLinearEquiv (R := 𝕜) (A := A) (n := Fin N)
    have he : e.symm (Lie.targetMapLinear uG A x) = e.symm (Lie.targetMapLinear uG A y) := h
    exact (Lie.targetMapLinear_injective uG A) (e.symm.injective he)

private theorem matrixUnit_mem_blockRadical (X : Mat) :
    GeneralLinear.DualNumber.matrixUnit X ∈ blockUnipotentSubgroup (DualNumber A) wt ↔
      ∀ i j, wt i ≤ wt j → X i j = 0 := by
  rw [mem_blockUnipotentSubgroup]
  simp only [GeneralLinear.DualNumber.matrixUnit_val, Matrix.add_apply,
    GeneralLinear.DualNumber.epsilonMatrix_apply]
  refine ⟨fun h i j hij => ?_, fun h i j hij => ?_⟩
  · exact congrArg TrivSqZeroExt.snd (add_left_cancel ((h i j hij).trans (add_zero _).symm))
  · rw [h i j hij, TrivSqZeroExt.inr_zero, add_zero]

omit [NumberField F] in
private theorem radicalTangentMatrix_mem_range (X : Mat) :
    X ∈ LinearMap.range (radicalTangentMatrix F r t A) ↔ ∀ i j, wt i ≤ wt j → X i j = 0 := by
  let e := GeneralLinear.DualNumber.pointKernelLinearEquiv (R := 𝕜) (A := A) (n := Fin N)
  let x := (e X).toMul.val
  have hx : affinePointsEquiv (Fin N) 𝕜 Sε x = GeneralLinear.DualNumber.matrixUnit X :=
    GeneralLinear.DualNumber.pointUnit_matrix X
  have h : x ∈ (blockUnipotent (Fin N) 𝕜 wt).carrier _ ↔ ∀ i j, wt i ≤ wt j → X i j = 0 := by
    rw [blockUnipotent, mem_ofMatrixSubgroups_affinePoints_iff
      (hH := fun f _ hf => map_mem_blockUnipotentSubgroup wt f.hom hf), hx, matrixUnit_mem_blockRadical]
  refine ⟨?_, ?_⟩
  · rintro ⟨Y, rfl⟩
    apply h.mp
    change (e ((radicalTangentMatrix F r t A) Y)).toMul.val ∈ _
    have he : e ((radicalTangentMatrix F r t A) Y) = Lie.targetMapLinear uG A Y :=
      e.apply_symm_apply _
    rw [he, lieKernelTargetLinear_val, ← (isRepresentedBy_blockUnipotent (Fin N) 𝕜 wt).2]
    exact ⟨Y.toMul.val, rfl⟩
  · intro hX
    have hy := h.mpr hX
    rw [← (isRepresentedBy_blockUnipotent (Fin N) 𝕜 wt).2] at hy
    obtain ⟨y, hy⟩ := hy
    change y ≫ (uG).hom.hom = x at hy
    have hy' : y ∈ lieKernel U A := by
      apply mem_lieKernel_of_comp uG y
      rw [hy]
      exact (e X).toMul.property
    refine ⟨Additive.ofMul ⟨y, hy'⟩, ?_⟩
    apply e.injective
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hy

omit [NumberField F] in
private def radicalTangentCoordinates : DU ≃ₗ[A] (UpperEntries r t → A) := by
  classical
  let T := radicalTangentMatrix F r t A
  let L : DU →ₗ[A] (UpperEntries r t → A) :=
    { toFun := fun x ij => T x ij.val.1 ij.val.2
      map_add' x y := by ext ij; exact congrArg (fun Z : Mat => Z ij.val.1 ij.val.2) (T.map_add x y)
      map_smul' c x := by
        ext ij
        exact congrArg (fun Z : Mat => Z ij.val.1 ij.val.2) (T.map_smul c x) }
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro x y h
    apply radicalTangentMatrix_injective
    ext i j
    by_cases hij : wt j < wt i
    · exact congrFun h ⟨(i, j), hij⟩
    · exact ((radicalTangentMatrix_mem_range F r t A (T x)).mp ⟨x, rfl⟩ i j (le_of_not_gt hij)).trans
        (((radicalTangentMatrix_mem_range F r t A (T y)).mp ⟨y, rfl⟩ i j (le_of_not_gt hij)).symm)
  · intro f
    let X : Mat := Matrix.of fun i j => if hij : wt j < wt i then f ⟨(i, j), hij⟩ else 0
    obtain ⟨y, hy⟩ := (radicalTangentMatrix_mem_range F r t A X).mpr
      (fun i j hij => dite_eq_right (not_lt_of_ge hij))
    refine ⟨y, funext fun ij => ?_⟩
    change T y ij.val.1 ij.val.2 = _
    rw [hy]
    exact dite_eq_left ij.property

omit [NumberField F] in
private theorem radicalTangentCoordinates_apply (x : DU) (ij : UpperEntries r t) :
    radicalTangentCoordinates F r t A x ij = radicalTangentMatrix F r t A x ij.val.1 ij.val.2 := rfl

end Coordinates

private def upperEntriesEquiv : Fin (r + 1) × Fin (t + 1) ≃ UpperEntries r t := by
  let f : Fin (r + 1) × Fin (t + 1) → UpperEntries r t := fun x =>
    ⟨((B).index (firstBlock r t) x.1, (B).index (secondBlock r t) x.2), (blockShapeWeight_lt_iff B (i := secondBlock r t) (j := firstBlock r t) x.2 x.1).mpr (by change (0 : ℕ) < 1; omega)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Prod.ext (((B).index (firstBlock r t)).injective (congrArg (fun ij : UpperEntries r t => ij.val.1) h))
      (((B).index (secondBlock r t)).injective (congrArg (fun ij : UpperEntries r t => ij.val.2) h))
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨i, x, rfl⟩ := exists_eq_index B a
    obtain ⟨j, y, rfl⟩ := exists_eq_index B b
    have hij := (blockShapeWeight_lt_iff B y x).mp hab
    have hi : i = firstBlock r t := by
      have hj₂ : j.val < 2 := j.isLt
      apply Fin.ext
      change i.val < j.val at hij
      change i.val = 0
      omega
    have hj : j = secondBlock r t := by
      have h₂ : j.val < 2 := j.isLt
      apply Fin.ext
      change i.val < j.val at hij
      change j.val = 1
      omega
    subst i j
    exact ⟨(x, y), rfl⟩

section ScalarAction

variable (A : Type) [CommRing A] [Algebra F A]

local notation "S" => CommAlgCat.of F A
local notation "action" => centralizerAdjointAction (hM) (hU)
local notation "aGL" => affinePointsEquiv (Fin N) 𝕜 S

omit [NumberField F] in
private theorem radicalTangentMatrix_differential (m : Lie.AffinePoints M A)
    (x : Additive (lieKernel U A)) :
    radicalTangentMatrix F r t A ((action).differential m x) =
      ((aGL) (m ≫ (mG).hom.hom)).val * radicalTangentMatrix F r t A x *
        (((aGL) (m ≫ (mG).hom.hom))⁻¹ : GL (Fin N) A).val := by
  let e := GeneralLinear.DualNumber.pointKernelLinearEquiv (R := 𝕜) (A := A) (n := Fin N)
  have h (y : Additive (lieKernel U A)) :
      e (radicalTangentMatrix F r t A y) = Lie.targetMapLinear uG A y := e.apply_symm_apply _
  apply e.injective
  rw [h, ← GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, h]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [lieKernelTargetLinear_val, AutomorphicAction.differential_val,
    centralizerAdjointAction_act_comp, adjoint_val, lieKernelTargetLinear_val]
  rfl

omit [NumberField F] in
private theorem leviEmbedding_scalar_diagonal (z : Fin ((B).length) → Aˣ) :
    ((B).leviEmbedding A (fun i => Matrix.GeneralLinearGroup.scalar (Fin ((B).size i)) (z i))).val =
      Matrix.diagonal (fun j => (z ((B).coordinateBlock j)).val) := by
  ext i j
  obtain ⟨k, a, rfl⟩ := exists_eq_index B i
  obtain ⟨k', b, rfl⟩ := exists_eq_index B j
  by_cases h : k = k'
  · subst k'
    rw [(B).leviEmbedding_apply_same, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change _ = if (B).index k a = (B).index k b then
      (z ((B).coordinateBlock ((B).index k a))).val else 0
    have he : (B).coordinateBlock ((B).index k a) = k := by
      unfold Langlands.GeneralLinear.BlockShape.coordinateBlock
      exact congrArg Sigma.fst ((B).indexEquiv.symm_apply_apply ⟨k, a⟩)
    rw [he]
    change (if a = b then (z k).val else 0) = _
    by_cases hab : a = b
    · subst b
      simp only [ite_true]
    · simp only [hab, ((B).index k).injective.ne hab, ite_false]
  · rw [(B).leviEmbedding_apply_ne _ _ _ _ h, Matrix.diagonal_apply_ne]
    exact fun e => h (congrArg Sigma.fst ((index_eq_index_iff B a b).mp e))

omit [NumberField F] in
private theorem radical_differential_eq_smul (m : Lie.AffinePoints M A) (z : Fin ((B).length) → Aˣ)
    (hm : ∀ i : Fin ((B).length), blockLeviAffineEquiv F B S m i =
      Matrix.GeneralLinearGroup.scalar (Fin ((B).size i)) (z i)) :
    ((action).differential m).toLinearMap = (((z i₀ / z i₁ : Aˣ) : A) • LinearMap.id : Module.End A (Additive (lieKernel U A))) := by
  have hcoord (k : Fin ((B).length)) (a : Fin ((B).size k)) :
      (B).coordinateBlock ((B).index k a) = k := by
    unfold Langlands.GeneralLinear.BlockShape.coordinateBlock
    exact congrArg Sigma.fst ((B).indexEquiv.symm_apply_apply ⟨k, a⟩)
  have hdiag : ((aGL) (m ≫ (mG).hom.hom)).val =
      Matrix.diagonal (fun j => (z ((B).coordinateBlock j)).val) := by
    change (affinePointsEquiv (Fin N) 𝕜 S ((M).affinePointsTarget mG S m)).val = _
    rw [← leviEmbedding_blockLeviAffineEquiv, funext hm, leviEmbedding_scalar_diagonal]
  have hdiag_inv : (((aGL) (m ≫ (mG).hom.hom))⁻¹ : GL (Fin N) A).val =
      Matrix.diagonal (fun j => ((z ((B).coordinateBlock j))⁻¹).val) := by
    have hm' : blockLeviAffineEquiv F B S m⁻¹ = fun i =>
        Matrix.GeneralLinearGroup.scalar (Fin ((B).size i)) ((z i)⁻¹) := by
      rw [map_inv, funext hm]
      funext i
      exact (map_inv _ _).symm
    change (((aGL) ((M).affinePointsTarget mG S m))⁻¹ : GL (Fin N) A).val = _
    rw [← map_inv, ← map_inv, ← leviEmbedding_blockLeviAffineEquiv, hm',
      leviEmbedding_scalar_diagonal]
  apply LinearMap.ext
  intro x
  apply (radicalTangentCoordinates F r t A).injective
  funext ij
  obtain ⟨⟨a, b⟩, rfl⟩ := (upperEntriesEquiv r t).surjective ij
  simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul, radicalTangentCoordinates_apply]
  rw [radicalTangentMatrix_differential, hdiag, hdiag_inv,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (z ((B).coordinateBlock ((B).index (firstBlock r t) a))).val *
      radicalTangentMatrix F r t A x ((B).index (firstBlock r t) a) ((B).index (secondBlock r t) b) *
        ((z ((B).coordinateBlock ((B).index (secondBlock r t) b)))⁻¹).val =
      ((z i₀ / z i₁ : Aˣ) : A) * radicalTangentMatrix F r t A x ((B).index i₀ a) ((B).index i₁ b)
  rw [hcoord, hcoord]
  simp only [div_eq_mul_inv, Units.val_mul]
  ring

end ScalarAction


local notation "A" => Adeles F
local notation "S" => CommAlgCat.of F A

private theorem adjointDeterminant_at_blockScalar (m : AdelicGroupPoints F M) (z : Fin ((B).length) → Ideles F)
    (hm : ∀ i : Fin ((B).length), matrixLeviPoint F B m i = AdelicGL.scalar F ((B).size i) (z i)) :
    characterUnits F P (Lie.adjointDeterminantCharacter P).toMul S (map F M P l m) =
      (z i₀ / z i₁) ^ ((r + 1) * (t + 1)) := by
  let e := radicalTangentCoordinates F r t A
  classical
  let c := Lie.finiteCoordinates M
  let : Module.Free A (Additive (lieKernel U A)) := Module.Free.of_equiv e.symm
  let : Module.Finite A (Additive (lieKernel U A)) := Module.Finite.equiv e.symm
  let : Module.Free A (Additive (lieKernel M A)) := Module.Free.of_equiv (c.equiv S).symm
  let : Module.Finite A (Additive (lieKernel M A)) := Module.Finite.equiv (c.equiv S).symm
  have hl : map F M P l m = m ≫ (centralizerToParabolic (hP) (hM)).hom.hom := by
    let : Mono (p).hom.hom := (hP).1
    apply (cancel_mono (p).hom.hom).mp
    change (m ≫ (l).hom.hom) ≫ (p).hom.hom =
      (m ≫ (centralizerToParabolic (hP) (hM)).hom.hom) ≫ (p).hom.hom
    simp only [Category.assoc, ← Grp.comp_hom_hom, blockLeviInclusion_comp,
      centralizerToParabolic_comp]
  have hMdet : LinearEquiv.det ((AutomorphicAction.conjugation (𝟙 M)).differential m) = 1 := by
    rw [← Lie.adjointDeterminantCharacter_affinePoints M S,
      Lie.connectedReductiveAdjointDeterminant F M (blockLevi_isConnectedReductive F B),
      rationalCharacters.comp_zero, map_one]
  change Gm.affinePointsEquiv ((algSpec 𝕜).obj (op S)).hom
    (map F M P l m ≫ (Lie.adjointDeterminantCharacter P).toMul.hom.hom) = _
  rw [Lie.adjointDeterminantCharacter_affinePoints P S, hl,
    det_conjugation_centralizerToParabolic (hP) (hM) (hU), hMdet, mul_one]
  apply Units.ext
  let b := (Pi.basisFun A (UpperEntries r t)).map e.symm
  rw [LinearEquiv.coe_det, radical_differential_eq_smul F r t A m z hm,
    ← LinearMap.det_toMatrix b, map_smul, LinearMap.toMatrix_id, Matrix.det_smul,
    Matrix.det_one, mul_one, ← Fintype.card_congr (upperEntriesEquiv r t),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Units.val_pow_eq_pow_val]

/-- On block scalar Levi points, the scheme half modulus is the positive matrix half modulus. -/
theorem parameterPower_halfModulus_of_blockScalar (m : AdelicGroupPoints F M) (z : Fin ((B).length) → Ideles F)
    (hm : ∀ i : Fin ((B).length), matrixLeviPoint F B m i = AdelicGL.scalar F ((B).size i) (z i)) :
    parameterPower F P (halfModulusParameter F P) (map F M P l m) =
      (leviHalfCharacter F B (matrixLeviPoint F B m) : ℂ) := by
  let q := map F M P l m
  have hchar : characterNorm F P (Lie.adjointDeterminantCharacter P).toMul q =
      leviCharacter F B (matrixLeviPoint F B m) := by
    change IdeleAbsoluteValue.full F
      (characterUnits F P (Lie.adjointDeterminantCharacter P).toMul S q) = _
    rw [adjointDeterminant_at_blockScalar F r t m z hm, map_pow, map_div,
      leviCharacter_apply, prod_blocks, prod_filter_firstBlock, prod_filter_secondBlock, mul_one,
      hm (firstBlock r t), hm (secondBlock r t), determinantNorm_scalar, determinantNorm_scalar,
      ← pow_mul, ← pow_mul, div_pow]
    change _ = (IdeleAbsoluteValue.full F (z i₀)) ^ ((r + 1) * (t + 1)) /
      (IdeleAbsoluteValue.full F (z i₁)) ^ ((t + 1) * (r + 1))
    rw [Nat.mul_comm (t + 1) (r + 1)]
  rw [parameterPower, halfModulusParameter, complexParameterPairing_tmul, characterLog_apply,
    hchar, coe_leviHalfCharacter, Real.coe_sqrt, Real.sqrt_eq_rpow]
  let s : ℝ := ((leviCharacter F B (matrixLeviPoint F B m) : ℝ≥0) : ℝ)
  have hs : 0 < s := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  change Complex.exp ((1 / 2) * ((Real.log s : ℝ) : ℂ)) = (↑(s ^ (1 / (2 : ℝ))) : ℂ)
  rw [Real.rpow_def_of_pos hs, Complex.ofReal_exp]
  push_cast
  ring_nf

end Langlands.Global.CuspidalPairEisenstein
