import Langlands.Automorphic.BlockShapeLeviSlices
import Langlands.Automorphic.CuspidalWhittaker.ArchimedeanFunctional
import Langlands.Global.ArchimedeanComplexLieCoordinates

/-! # The strict upper block enveloping ideal annihilates the Levi restriction -/

noncomputable section

universe u

open scoped Classical Matrix.Norms.Operator TensorProduct CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open _root_.AlgebraicGeometry NumberField Langlands.Algebra Langlands.Algebra.UniversalEnveloping
  Langlands.Archimedean Langlands.Archimedean.Kostant Langlands.Geometric
  Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear
  Langlands.Automorphic.CuspidalWhittaker
  Global.RankinSelbergGlobal.WhittakerCurve

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance positiveEnvelopingRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance positiveEnvelopingContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance positiveEnvelopingFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance positiveEnvelopingAffine : IsAffine (G).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance positiveEnvelopingSmooth : Smooth (G).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local notation "R" => mixedEmbedding.mixedSpace F
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Λ" => ComplexLieMatrixPlace F
local notation "e" => complexLieProductMatrixCoordinates F n

/-- The normalized period at actual Levi points, as a linear map of the original functions. -/
def blockLeviTermRestriction : V →ₗ[ℂ] (M → ℂ) where
  toFun f := blockShapeLeviSlice F B f 1
  map_add' f g := funext fun _m => congrFun
    (map_add (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) f g) _
  map_smul' z f := funext fun _m => congrFun
    (map_smul (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) z f) _

private def realEntryDirection (a b : Fin n) (c : R) : RealLieAlgebra F n :=
  (realLieAlgebraToMatrix F n).symm (Matrix.single a b c)

private theorem infiniteEntryCurve_apply_eq_one (a b : Fin n) (hab : a ≠ b) (c : R)
    (x y : Fin n) (hxy : ¬(a = x ∧ b = y)) (t : ℝ) :
    infiniteOneParameter F n (realEntryDirection F a b c) t x y =
      (1 : Matrix (Fin n) (Fin n) (InfiniteAdeles F)) x y := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  change (archimedeanGLCoordinates F n
      (infiniteOneParameter F n (realEntryDirection F a b c) t)).val x y = _
  rw [infiniteOneParameter, ContinuousMulEquiv.apply_symm_apply, oneParameter_val,
    show realLieAlgebraToMatrix F n (realEntryDirection F a b c) = Matrix.single a b c from
      (realLieAlgebraToMatrix F n).apply_symm_apply _,
    exp_smul_of_mul_self_eq_zero (Matrix.single_mul_single_of_ne c a b a hab.symm c),
    Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply_of_ne a b c x y hxy, smul_zero, add_zero]
  simp only [Matrix.one_apply]
  split_ifs
  · exact (map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)).symm
  · exact (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)).symm

private theorem adelicEntryCurve_mem_radical (a b : Fin n) (hab : blockIndex B a < blockIndex B b)
    (c : R) (t : ℝ) :
    AdelicGL.ofInfinite F n (infiniteOneParameter F n (realEntryDirection F a b c) t) ∈
      B.unipotentSubgroup (Adeles F) := by
  let g := AdelicGL.ofInfinite F n (infiniteOneParameter F n (realEntryDirection F a b c) t)
  have hn : a ≠ b := fun h => hab.ne (congrArg (blockIndex B) h)
  have h (x y : Fin n) (hxy : ¬blockIndex B x < blockIndex B y) :
      (g : Matrix (Fin n) (Fin n) (Adeles F)) x y = (1 : Matrix (Fin n) (Fin n) (Adeles F)) x y := by
    have he := infiniteEntryCurve_apply_eq_one F a b hn c x y
      (fun ⟨ha, hb⟩ => hxy (ha ▸ hb ▸ hab)) t
    change (AdelicGL.ofInfinite F n (infiniteOneParameter F n (realEntryDirection F a b c) t)).val x y = _
    rw [ofInfinite_val_apply, he]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  apply (B.mem_unipotentSubgroup_iff (Adeles F) g).2
  constructor
  · apply (B.mem_parabolic_iff (Adeles F) g).2
    intro i j x y hij
    rw [h _ _ (by simpa only [blockIndex_index] using (not_lt.mpr hij.le : ¬i < j)), Matrix.one_apply_ne]
    intro he
    exact hij.ne ((blockIndex_index B j y).symm.trans
      ((congrArg (blockIndex B) he).symm.trans (blockIndex_index B i x)))
  · intro i x y
    rw [h _ _ (by simp), Matrix.one_apply]
    simp only [(B.index i).injective.eq_iff]

private theorem blockLeviTermRestriction_realEntry_eq_zero (a b : Fin n)
    (hab : blockIndex B a < blockIndex B b) (c : R) (f : V) :
    blockLeviTermRestriction F B
      (finiteSmoothEnvelopingAction F n
        (envelopingGenerator F n (complexify F n (realEntryDirection F a b c))) f) = 0 := by
  funext m
  let X := realEntryDirection F a b c
  let h := fun t => AdelicGL.ofInfinite F n (infiniteOneParameter F n X t)
  let g := B.leviEmbedding (Adeles F) m
  let coord := GeneralLinearGroupPoints.adelicEquiv F n
  have hd : HasDerivAt (fun s => blockShapeConstantTerm B F f (g * h s))
      (blockShapeConstantTerm B F (finiteSmoothEnvelopingAction F n
        (envelopingGenerator F n (complexify F n X)) f) g) 0 := by
    simpa only [blockShapeConstantTerm, map_mul, h, g, coord, adelicOneParameter,
      infiniteOneParameter_zero, map_one, mul_one] using
      finiteSmoothBlockConstantTerm_hasDerivAt F (standardBlockWeight B.cuts) X f (coord.symm g) 0
  have hfun : (fun s : ℝ => blockShapeConstantTerm B F f (g * h s)) =
      fun _ : ℝ => blockShapeConstantTerm B F f g := by
    funext t
    obtain ⟨p, hp, he⟩ := adelicEntryCurve_mem_radical F B a b hab c t
    have hval : p.val = h t := he
    have hproj : B.leviProjection (Adeles F) p = 1 := hp
    have hcov := blockShapeLeviSlice_parabolic_mul F B f p 1 m
    rw [hproj, mul_one] at hcov
    simpa only [g, ← hval, blockShapeLeviSlice, mul_one] using hcov
  rw [hfun] at hd
  simpa only [blockLeviTermRestriction, LinearMap.coe_mk, AddHom.coe_mk, blockShapeLeviSlice,
    mul_one, Pi.zero_apply, X, g] using hd.unique (hasDerivAt_const 0 (blockShapeConstantTerm B F f g))

private def realEntryProjection (a b : Fin n) : RealLieAlgebra F n →ₗ[ℝ] RealLieAlgebra F n :=
  (realLieAlgebraToMatrix F n).symm.toLinearMap ∘ₗ Matrix.singleLinearMap ℝ a b ∘ₗ
    Matrix.entryLinearMap ℝ R a b ∘ₗ (realLieAlgebraToMatrix F n).toLinearMap

omit [NumberField F] in
private theorem realEntryProjection_matrix (a b : Fin n) (X : RealLieAlgebra F n) :
    realLieAlgebraToMatrix F n (realEntryProjection F a b X) =
      Matrix.single a b (realLieAlgebraToMatrix F n X a b) :=
  (realLieAlgebraToMatrix F n).apply_symm_apply _

private theorem matrixCoordinates_entryProjection (a b : Fin n) (X : ComplexLieAlgebra F n) (v : Λ) :
    e ((realEntryProjection F a b).baseChange ℂ X) v = Matrix.single a b (e X v a b) := by
  induction X using TensorProduct.inductionOn with
  | add X Y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, Matrix.add_apply,
      Matrix.single_add]
  | tmul z X =>
    rw [LinearMap.baseChange_tmul]
    cases v with
    | inl v =>
      rw [complexLieProductMatrixCoordinates_tmul_real, complexLieProductMatrixCoordinates_tmul_real]
      have hm : realPlaceLieProjection F n v (realEntryProjection F a b X) =
          Matrix.single a b (realPlaceLieProjection F n v X a b) := by
        change (realLieAlgebraToMatrix F n (realEntryProjection F a b X)).map
          (realPlaceScalarProjection F v) = _
        rw [realEntryProjection_matrix, Matrix.map_single]
        rfl
      rw [hm, Matrix.map_single, Matrix.smul_single, Matrix.smul_apply]
      rfl
    | inr v =>
      obtain ⟨v, k⟩ := v
      rw [complexLieProductMatrixCoordinates_tmul_complex, complexLieProductMatrixCoordinates_tmul_complex]
      have hm : complexPlaceLieProjection F n v (realEntryProjection F a b X) =
          Matrix.single a b (complexPlaceLieProjection F n v X a b) := by
        change (realLieAlgebraToMatrix F n (realEntryProjection F a b X)).map
          (complexPlaceScalarProjection F v) = _
        rw [realEntryProjection_matrix, Matrix.map_single]
        rfl
      rw [hm]
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · simp only [ComplexGenericLarge.pairHom_zero, Matrix.smul_single, Matrix.smul_apply]
      · simp only [ComplexGenericLarge.pairHom_one, Matrix.map_single, Matrix.smul_single,
          Matrix.smul_apply]
        rfl

private theorem blockLeviTermRestriction_complexEntry_eq_zero (a b : Fin n)
    (hab : blockIndex B a < blockIndex B b) (X : ComplexLieAlgebra F n) (f : V) :
    blockLeviTermRestriction F B (finiteSmoothEnvelopingAction F n
      (envelopingGenerator F n ((realEntryProjection F a b).baseChange ℂ X)) f) = 0 := by
  induction X using TensorProduct.inductionOn with
  | add X Y hx hy =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, map_add, hx, hy, add_zero]
  | tmul z X =>
    rw [LinearMap.baseChange_tmul,
      show z ⊗ₜ[ℝ] realEntryProjection F a b X = z • complexify F n (realEntryProjection F a b X) by
        rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, map_smul, LinearMap.smul_apply, map_smul]
    rw [show realEntryProjection F a b X = realEntryDirection F a b (realLieAlgebraToMatrix F n X a b)
      from rfl, blockLeviTermRestriction_realEntry_eq_zero F B a b hab, smul_zero]

local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : Λ => n))

/-- The genuine finite-smooth action transported to the actual complex matrix product. -/
def finiteSmoothMatrixEnvelopingAction : U →ₐ[ℂ] Module.End ℂ V :=
  (finiteSmoothEnvelopingAction F n).comp (LieEnvelopingEquiv.enveloping (e).symm).toAlgHom

private theorem blockLeviTermRestriction_matrixUnit_eq_zero (v : Λ) (a b : Fin n)
    (hab : blockIndex B a < blockIndex B b) (f : V) :
    blockLeviTermRestriction F B (finiteSmoothMatrixEnvelopingAction F
      (UniversalEnvelopingAlgebra.ι ℂ (glBasis ℂ (fun _ : Λ => n) ⟨v, a, b⟩)) f) = 0 := by
  let X := (e).symm (glBasis ℂ (fun _ : Λ => n) ⟨v, a, b⟩)
  have hfix : (realEntryProjection F a b).baseChange ℂ X = X := by
    apply (e).injective
    funext w
    change e ((realEntryProjection F a b).baseChange ℂ X) w = e X w
    rw [matrixCoordinates_entryProjection, show e X = glBasis ℂ (fun _ : Λ => n) ⟨v, a, b⟩ from
      (e).apply_symm_apply _, glBasis_apply]
    by_cases hw : w = v
    · subst w
      simp [unit]
    · simp [unit, Pi.single_eq_of_ne hw]
  rw [finiteSmoothMatrixEnvelopingAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    LieEnvelopingEquiv.enveloping_generator]
  have h := blockLeviTermRestriction_complexEntry_eq_zero F B a b hab X f
  rw [hfix] at h
  exact h

/-- At actual Levi points, the period annihilates the right ideal generated by strict upper
block Lie directions. -/
theorem blockLeviTermRestriction_positiveIdeal_eq_zero (f : V) {u : U}
    (hu : u ∈ positiveWeightRightIdeal (glBasis ℂ (fun _ : Λ => n)) (blockAdjointWeight B Λ)) :
    blockLeviTermRestriction F B (finiteSmoothMatrixEnvelopingAction F u f) = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨⟨v, a, b⟩, hab, y, rfl⟩ := hu
    rw [map_mul, Module.End.mul_apply]
    exact blockLeviTermRestriction_matrixUnit_eq_zero F B v a b
      ((blockAdjointWeight_pos_iff B (⟨v, a, b⟩ : Coord (fun _ : Λ => n))).mp hab) _
  | zero => rw [map_zero, LinearMap.zero_apply, map_zero]
  | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply, map_add, hu, hv, add_zero]
  | smul c u _ hu => rw [map_smul, LinearMap.smul_apply, map_smul, hu, smul_zero]

end Langlands.Automorphic
