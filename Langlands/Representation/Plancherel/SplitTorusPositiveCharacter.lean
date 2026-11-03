import Langlands.Representation.Plancherel.SplitTorusRealPart
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.BruhatTits.Cartan.CentralizerValuationConsequences
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Positive smooth characters of actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The positive complex character attached to an actual real character parameter. -/
def positiveCharacter (hA : IsSplitTorus A.toGrp) (phi : RealTorusSpace.Vstar A) :
    rationalPoints A.toGrp →* ℂˣ where
  toFun a := Units.mk0
    (Real.exp (-RealTorusSpace.pair A phi (valuation hA a).toAdd *
      Real.log (LocalField.residueCardinality F : ℝ)) : ℂ)
    (by exact_mod_cast Real.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [map_mul, toAdd_mul, map_add, neg_add, add_mul, Real.exp_add,
      Complex.ofReal_mul, Units.val_mul, Units.val_mk0]

@[simp] theorem positiveCharacter_val (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    (positiveCharacter hA phi a : ℂ) =
      (Real.exp (-RealTorusSpace.pair A phi (valuation hA a).toAdd *
        Real.log (LocalField.residueCardinality F : ℝ)) : ℂ) := rfl

theorem positiveCharacter_norm (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    ‖(positiveCharacter hA phi a : ℂ)‖ =
      (LocalField.residueCardinality F : ℝ) ^
        (-RealTorusSpace.pair A phi (valuation hA a).toAdd) := by
  rw [positiveCharacter_val, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.rpow_def_of_pos (by
    exact_mod_cast (LocalField.residueCardinality_gt_one F).trans' Nat.zero_lt_one)]
  congr 1
  ring

theorem positiveCharacter_re_pos (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    0 < (positiveCharacter hA phi a : ℂ).re :=
  Real.exp_pos _

theorem positiveCharacter_im (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) (a : rationalPoints A.toGrp) :
    (positiveCharacter hA phi a : ℂ).im = 0 := rfl

@[simp] theorem positiveCharacter_zero (hA : IsSplitTorus A.toGrp) :
    positiveCharacter hA (0 : RealTorusSpace.Vstar A) = 1 := by
  ext a
  simp [positiveCharacter]

theorem positiveCharacter_add (hA : IsSplitTorus A.toGrp)
    (phi psi : RealTorusSpace.Vstar A) :
    positiveCharacter hA (phi + psi) =
      positiveCharacter hA phi * positiveCharacter hA psi := by
  apply MonoidHom.ext
  intro a
  apply Units.ext
  change (Real.exp (-RealTorusSpace.pair A (phi + psi) (valuation hA a).toAdd *
    Real.log (LocalField.residueCardinality F : ℝ)) : ℂ) =
      (Real.exp (-RealTorusSpace.pair A phi (valuation hA a).toAdd *
        Real.log (LocalField.residueCardinality F : ℝ)) : ℂ) *
      (Real.exp (-RealTorusSpace.pair A psi (valuation hA a).toAdd *
        Real.log (LocalField.residueCardinality F : ℝ)) : ℂ)
  rw [map_add, LinearMap.add_apply, neg_add, add_mul, Real.exp_add, Complex.ofReal_mul]

theorem positiveCharacter_neg (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    positiveCharacter hA (-phi) = (positiveCharacter hA phi)⁻¹ := by
  have h := positiveCharacter_add hA phi (-phi)
  rw [add_neg_cancel, positiveCharacter_zero] at h
  apply MonoidHom.ext
  intro a
  exact eq_inv_of_mul_eq_one_right (DFunLike.congr_fun h.symm a)

/-- The existing positive valuation of the intrinsic section is the embedded cocharacter. -/
theorem valuation_latticeSection (hA : IsSplitTorus A.toGrp)
    (c : cocharacterLattice A) :
    (valuation hA (CocharacterUniformizer.latticeSection F A
      (Multiplicative.ofAdd c))).toAdd = (1 : ℝ) ⊗ₜ[ℤ] c := by
  symm
  apply (BruhatTits.Cartan.eq_centralizerValuation_iff _ _ _ _).mpr
  intro χ
  rw [BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply, RealTorusSpace.eval_tmul, one_mul]
  have h := CocharacterUniformizer.rationalCharacterValuation_latticeSection F A
    (rationalCharacters.equivCharacterLattice A χ) c
  simpa using (congrArg (fun n : ℤ => (n : ℝ)) h).symm

/-- The parameter of the positive character is exactly its supplied real parameter. -/
@[simp] theorem normalizedRealPart_positiveCharacter (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    normalizedRealPart hA (positiveCharacter hA phi) = phi := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A (normalizedRealPart hA (positiveCharacter hA phi))
    (r ⊗ₜ[ℤ] c) = RealTorusSpace.pair A phi (r ⊗ₜ[ℤ] c)
  rw [pair_normalizedRealPart_tmul]
  have hc : sectionLog (positiveCharacter hA phi) c =
      RealTorusSpace.pair A phi ((1 : ℝ) ⊗ₜ[ℤ] c) := by
    change -Real.log ‖(positiveCharacter hA phi
      (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)) : ℂ)‖ /
      Real.log (LocalField.residueCardinality F : ℝ) = _
    rw [positiveCharacter_val, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.log_exp, valuation_latticeSection,
      neg_mul, neg_neg]
    apply mul_div_cancel_right₀
    exact (Real.log_pos (by
      exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'
  rw [hc, show (r ⊗ₜ[ℤ] c : RealTorusSpace.V A) =
    r • ((1 : ℝ) ⊗ₜ[ℤ] c) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, smul_eq_mul]

theorem rawLogRealPart_positiveCharacter (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    rawLogRealPart hA (positiveCharacter hA phi) =
      (-Real.log (LocalField.residueCardinality F : ℝ)) • phi := by
  rw [rawLogRealPart, normalizedRealPart_positiveCharacter]

theorem positiveCharacter_trivial_on_normKernel (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) {a : rationalPoints A.toGrp}
    (ha : a ∈ rationalCommonNormKernel A.toGrp) :
    positiveCharacter hA phi a = 1 := by
  have hv : valuation hA a = 1 := by
    exact (show a ∈ (valuation hA).ker from
      (BruhatTits.Cartan.centralizerValuation_ker (𝟙 A.toGrp)
        (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA)).symm ▸ ha)
  apply Units.ext
  simp [positiveCharacter_val, hv]

section CanonicalTopology

variable [IsAffine A.X.left]

local instance positivePointTopology : TopologicalSpace (rationalPoints A.toGrp) :=
  rationalPointTopology F A.X

/-- Every real parameter gives a smooth character for the canonical point topology. -/
theorem isOpen_ker_positiveCharacter (hA : IsSplitTorus A.toGrp)
    (phi : RealTorusSpace.Vstar A) :
    IsOpen ((positiveCharacter hA phi).ker : Set (rationalPoints A.toGrp)) := by
  let : IsAffineHom A.X.hom := hA.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : Smooth A.X.hom := hA.smooth
  let : IsTopologicalGroup (rationalPoints A.toGrp) :=
    rationalPoint_isTopologicalGroup F A.toGrp
  exact Subgroup.isOpen_mono
    (fun _ ha => positiveCharacter_trivial_on_normKernel hA phi ha)
    (isOpen_rationalCommonNormKernel A.toGrp)

end CanonicalTopology

end Langlands.Plancherel.SplitTorus
