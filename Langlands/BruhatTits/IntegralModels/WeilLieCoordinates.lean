import Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange
import Langlands.BruhatTits.IntegralModels.WeilCongruenceModel
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints

/-! # Coefficients of tangent vectors of a multiplicative Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard
open Langlands.BruhatTits.IntegralModels
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.WeilGm

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Finite R B] [Module.Projective R B]

local notation "W" => groupScheme (CommRingCat.of R) B
local notation "P" => affineUnitsEquiv (CommRingCat.of R) B

/-- The multiplicative Weil restriction is affine over the base. -/
instance groupScheme_isAffineHom : IsAffineHom (W).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The units of `B[ε]` representing the affine dual-number points of the
multiplicative Weil restriction of `B` over `R`. -/
def dualUnitsEquiv : Lie.AffinePoints W (DualNumber R) ≃* (DualNumber B)ˣ :=
  (P (CommAlgCat.of R (DualNumber R))).trans
    (Units.mapEquiv (DualNumberBaseChange.tensorEquiv R B).toMulEquiv)

private theorem dualUnitsEquiv_reduction (x : Lie.AffinePoints W (DualNumber R)) :
    (Algebra.TensorProduct.rid R B B)
      (P (CommAlgCat.of R R) (Lie.reduction W x)).val =
      (dualUnitsEquiv R B x).val.fst := by
  let f : DualNumber R →ₐ[R] R := TrivSqZeroExt.fstHom R R R
  change (Algebra.TensorProduct.rid R B B)
      (P (CommAlgCat.of R R) (Lie.affineMap W f x)).val =
      (DualNumberBaseChange.tensorTo R B (P (CommAlgCat.of R (DualNumber R)) x).val).fst
  rw [Lie.affineMap_apply, affineUnitsEquiv_naturality (CommRingCat.of R) B
    (CommAlgCat.ofHom f)]
  let z := (P (CommAlgCat.of R (DualNumber R)) x).val
  change Algebra.TensorProduct.rid R B B
      (Algebra.TensorProduct.lTensor (S := B) B f z) =
    (DualNumberBaseChange.tensorTo R B z).fst
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.rid_tmul, DualNumberBaseChange.tensorTo_tmul,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl,
      GeneralLinear.DualNumber.coefficientMap_fst]
    rw [Algebra.smul_def, AlgHom.id_apply]
    exact mul_comm _ _
  | add x y hx hy => simp only [map_add, TrivSqZeroExt.fst_add, hx, hy]

/-- Identity reduction of an affine dual-number point is the constant coefficient condition. -/
theorem dualUnitsEquiv_fst_eq_one (x : Lie.AffinePoints W (DualNumber R)) :
    (dualUnitsEquiv R B x).val.fst = 1 ↔ Lie.reduction W x = 1 := by
  rw [← dualUnitsEquiv_reduction]
  let e := (P (CommAlgCat.of R R)).trans
    (Units.mapEquiv (Algebra.TensorProduct.rid R B B).toMulEquiv)
  change (e (Lie.reduction W x)).val = 1 ↔ _
  rw [← Units.val_one, Units.val_inj, ← e.map_one, e.injective.eq_iff]

private def lieCoefficient : Additive (lieKernel W R) →ₗ[R] B where
  toFun x := (dualUnitsEquiv R B x.toMul.val).val.snd
  map_add' x y := by
    change (dualUnitsEquiv R B (x.toMul.val * y.toMul.val)).val.snd =
      (dualUnitsEquiv R B x.toMul.val).val.snd + (dualUnitsEquiv R B y.toMul.val).val.snd
    rw [map_mul, Units.val_mul, DualNumber.snd_mul,
      (dualUnitsEquiv_fst_eq_one R B x.toMul.val).mpr x.toMul.property,
      (dualUnitsEquiv_fst_eq_one R B y.toMul.val).mpr y.toMul.property, one_mul, mul_one, add_comm]
  map_smul' a x := by
    let f := GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of R) a
    change (dualUnitsEquiv R B (Lie.affineMap W f x.toMul.val)).val.snd =
      a • (dualUnitsEquiv R B x.toMul.val).val.snd
    change (DualNumberBaseChange.tensorTo R B
      (P (CommAlgCat.of R (DualNumber R)) (Lie.affineMap W f x.toMul.val)).val).snd = _
    rw [Lie.affineMap_apply, affineUnitsEquiv_naturality (CommRingCat.of R) B
      (CommAlgCat.ofHom f)]
    let z := (P (CommAlgCat.of R (DualNumber R)) x.toMul.val).val
    change (DualNumberBaseChange.tensorTo R B
        (Algebra.TensorProduct.map (AlgHom.id R B) f z)).snd =
      a • (DualNumberBaseChange.tensorTo R B z).snd
    have h := DFunLike.congr_fun (DualNumberBaseChange.tensorTo_scale R B a) z
    change (DualNumberBaseChange.tensorTo R B)
        (Algebra.TensorProduct.map (AlgHom.id R B) f z) =
      GeneralLinear.DualNumber.epsilonScale (algebraMap R B a)
        (DualNumberBaseChange.tensorTo R B z) at h
    exact (congrArg TrivSqZeroExt.snd h).trans
      ((GeneralLinear.DualNumber.epsilonScale_snd _ _).trans (Algebra.smul_def ..).symm)

private theorem lieCoefficient_bijective : Function.Bijective (lieCoefficient R B) := by
  constructor
  · intro x y h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply (dualUnitsEquiv R B).injective
    apply Units.ext
    exact TrivSqZeroExt.ext
      (((dualUnitsEquiv_fst_eq_one R B x.toMul.val).mpr x.toMul.property).trans
        ((dualUnitsEquiv_fst_eq_one R B y.toMul.val).mpr y.toMul.property).symm) h
  · intro b
    let z : DualNumber B := ⟨1, b⟩
    have hu : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr isUnit_one
    let x := (dualUnitsEquiv R B).symm hu.unit
    have hx : (dualUnitsEquiv R B x).val = z :=
      (congrArg Units.val ((dualUnitsEquiv R B).apply_symm_apply hu.unit)).trans hu.unit_spec
    have hk : Lie.reduction W x = 1 :=
      (dualUnitsEquiv_fst_eq_one R B x).mp (congrArg TrivSqZeroExt.fst hx)
    exact ⟨Additive.ofMul ⟨x, hk⟩, congrArg TrivSqZeroExt.snd hx⟩

/-- A tangent vector is the first-order coefficient of its dual-number unit. -/
def lieCoefficientEquiv : Additive (lieKernel W R) ≃ₗ[R] B :=
  LinearEquiv.ofBijective (lieCoefficient R B) (lieCoefficient_bijective R B)

@[simp] theorem lieCoefficientEquiv_apply (x : Additive (lieKernel W R)) :
    lieCoefficientEquiv R B x = (dualUnitsEquiv R B x.toMul.val).val.snd := rfl

/-- The dual-number unit of `x` is `1 + ε b`, with `b` its Lie coordinate. -/
theorem dualUnitsEquiv_lieCoefficientEquiv (x : Additive (lieKernel W R)) :
    (dualUnitsEquiv R B x.toMul.val).val = ⟨1, lieCoefficientEquiv R B x⟩ :=
  TrivSqZeroExt.ext ((dualUnitsEquiv_fst_eq_one R B x.toMul.val).mpr x.toMul.property) rfl

variable {C : Type u} [CommRing C] [Algebra R C] [Module.Finite R C] [Module.Projective R C]

/-- On affine points a coefficient map acts on the left tensor factor. -/
theorem affineUnitsEquiv_coefficientMap (f : B →ₐ[R] C) (S : CommAlgCat (CommRingCat.of R))
    (x : (W).affinePoints S) :
    affineUnitsEquiv (CommRingCat.of R) C S (x ≫ (WeilCongruence.coefficientMap f).hom.hom) =
      Units.map (Algebra.TensorProduct.map f (AlgHom.id R S)).toMonoidHom (P S x) := by
  let A := CommRingCat.of R
  let T := (algSpec A).obj (op S)
  let c := (Corepresented.affineSectionsIso (R := A) S).hom.hom
  have hB := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor A B) (corepresentableBy A B) S x
  have hC := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor A C) (corepresentableBy A C) S (x ≫ (WeilCongruence.coefficientMap f).hom.hom)
  change Units.map (Algebra.TensorProduct.lTensor (S := B) B c).toMonoidHom
    (pointsEquiv A B T x) = P S x at hB
  change Units.map (Algebra.TensorProduct.lTensor (S := C) C c).toMonoidHom
    (pointsEquiv A C T (x ≫ (WeilCongruence.coefficientMap f).hom.hom)) =
      affineUnitsEquiv A C S (x ≫ (WeilCongruence.coefficientMap f).hom.hom) at hC
  rw [← hC, ← hB, WeilCongruence.coefficientMap_points]
  apply Units.ext
  let z := (pointsEquiv A B T x).val
  change Algebra.TensorProduct.lTensor (S := C) C c
      (Algebra.TensorProduct.map f (AlgHom.id R _) z) =
    Algebra.TensorProduct.map f (AlgHom.id R S) (Algebra.TensorProduct.lTensor (S := B) B c z)
  induction z using TensorProduct.inductionOn with
  | tmul b t => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A map of coefficient algebras applies the original map to both coefficients. -/
theorem dualUnitsEquiv_coefficientMap (f : B →ₐ[R] C) (x : Lie.AffinePoints W (DualNumber R)) :
    (dualUnitsEquiv R C (x ≫ (WeilCongruence.coefficientMap f).hom.hom)).val =
      GeneralLinear.DualNumber.coefficientMap f.toRingHom (dualUnitsEquiv R B x).val := by
  change DualNumberBaseChange.tensorTo R C
    (affineUnitsEquiv (CommRingCat.of R) C (CommAlgCat.of R (DualNumber R))
      (x ≫ (WeilCongruence.coefficientMap f).hom.hom)).val = _
  rw [affineUnitsEquiv_coefficientMap]
  exact DFunLike.congr_fun (DualNumberBaseChange.tensorTo_natural R f).symm
    (P (CommAlgCat.of R (DualNumber R)) x).val

/-- In tangent coordinates the differential of the coefficient map is the coefficient map. -/
theorem lieCoefficientEquiv_coefficientMap (f : B →ₐ[R] C) (x : Additive (lieKernel W R)) :
    lieCoefficientEquiv R C (Lie.targetMapLinear (WeilCongruence.coefficientMap f) R x) =
      f (lieCoefficientEquiv R B x) := by
  simp only [lieCoefficientEquiv_apply, lieKernelTargetLinear_val,
    dualUnitsEquiv_coefficientMap, GeneralLinear.DualNumber.coefficientMap_snd]
  rfl

end Langlands.GroupScheme.WeilGm
