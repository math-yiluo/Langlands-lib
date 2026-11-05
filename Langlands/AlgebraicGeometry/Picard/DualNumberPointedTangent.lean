import Langlands.AlgebraicGeometry.Picard.DualNumberPointedDeformations
import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationModule
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.Algebra.Group.TransferInstance

/-! # Intrinsic first-order modules at every actual line bundle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (M : LineBundle X)

local notation "preservation" => pullbackTensorComparisonIsIso

/-- The ordinary class of the canonical split lift of the specified bundle. -/
def splitLiftClass : OrdinaryLiftClasses f M preservation :=
  ⟨LineBundle.pullbackHom preservation (projection f) (LineBundle.isoClass preservation M), by
    rw [LineBundle.pullbackHom_comp_eq preservation (closedPoint f) (projection f)
      (closedPoint_projection f), LineBundle.pullbackHom_id]⟩

/-- Tensoring by the inverse split lift identifies every ordinary lift fibre
with the actual trivial-bundle deformation kernel. -/
def ordinaryTangentEquiv :
    OrdinaryLiftClasses f M preservation ≃ DeformationClasses preservation f where
  toFun q := ⟨q.val * (splitLiftClass f M).val⁻¹, by
    change LineBundle.pullbackHom preservation (closedPoint f) _ = 1
    rw [map_mul, map_inv, q.property, (splitLiftClass f M).property,
      mul_inv_cancel]⟩
  invFun t := ⟨t.val * (splitLiftClass f M).val, by
    rw [map_mul, (show LineBundle.pullbackHom preservation (closedPoint f) t.val = 1 from
      t.property), one_mul]
    exact (splitLiftClass f M).property⟩
  left_inv q := Subtype.ext (by simp [mul_assoc])
  right_inv t := Subtype.ext (by simp [mul_assoc])

/-- Actual pointed classes at `M`, normalized by its canonical split lift. -/
def pointedTangentEquiv :
    PointedDeformationClasses f M ≃ Additive (DeformationClasses preservation f) :=
  (pointedClassEquiv f M preservation).trans
    ((ordinaryTangentEquiv f M).trans Additive.ofMul)

lemma pointedTangentEquiv_val (q : PointedDeformationClasses f M) :
    (pointedTangentEquiv f M q).toMul.val =
      (pointedClassEquiv f M preservation q).val *
        (splitLiftClass f M).val⁻¹ := rfl

lemma pointedTangentEquiv_symm_val (t : Additive (DeformationClasses preservation f)) :
    (pointedClassEquiv f M preservation
      ((pointedTangentEquiv f M).symm t)).val =
        t.toMul.val * (splitLiftClass f M).val := by
  simp [pointedTangentEquiv, ordinaryTangentEquiv]

/-- Addition is tensor product normalized by the canonical split lift. -/
instance pointedClassesAddCommGroup : AddCommGroup (PointedDeformationClasses f M) :=
  (pointedTangentEquiv f M).addCommGroup

/-- The normalization is additive for the induced tensor operation. -/
def pointedTangentAddEquiv :
    PointedDeformationClasses f M ≃+ Additive (DeformationClasses preservation f) :=
  { pointedTangentEquiv f M with
    map_add' := fun _ _ ↦ (pointedTangentEquiv f M).apply_symm_apply _ }

lemma pointedClassEquiv_zero_val :
    (pointedClassEquiv f M preservation (0 : PointedDeformationClasses f M)).val =
      (splitLiftClass f M).val := by
  change (pointedClassEquiv f M preservation
    ((pointedTangentEquiv f M).symm 0)).val = _
  rw [pointedTangentEquiv_symm_val]
  exact one_mul _

private lemma normalized_mul {G : Type*} [CommGroup G] (a b c s : G)
    (h : a * s⁻¹ = (b * s⁻¹) * (c * s⁻¹)) :
    a = b * c * s⁻¹ := by
  apply mul_left_injective s⁻¹
  change a * s⁻¹ = (b * c * s⁻¹) * s⁻¹
  rw [h]
  simp only [mul_assoc]
  rw [mul_left_comm s⁻¹ c]

lemma pointedClassEquiv_add_val (q r : PointedDeformationClasses f M) :
    (pointedClassEquiv f M preservation (q + r)).val =
      (pointedClassEquiv f M preservation q).val *
        (pointedClassEquiv f M preservation r).val *
          (splitLiftClass f M).val⁻¹ := by
  have h := congrArg (fun t : Additive (DeformationClasses preservation f) ↦ t.toMul.val)
    ((pointedTangentAddEquiv f M).map_add q r)
  change _ * (splitLiftClass f M).val⁻¹ =
    ((_ * (splitLiftClass f M).val⁻¹) *
      (_ * (splitLiftClass f M).val⁻¹)) at h
  exact normalized_mul _ _ _ _ h

/-- Ordinary epsilon-scaling pullback retains the specified special-fibre class. -/
def scaleOrdinaryLiftClass (c : k) (q : OrdinaryLiftClasses f M preservation) :
    OrdinaryLiftClasses f M preservation :=
  ⟨LineBundle.pullbackHom preservation (scale f c) q.val, by
    rw [LineBundle.pullbackHom_comp_eq preservation (closedPoint f) (scale f c)
      (closedPoint_scale f c)]
    exact q.property⟩

/-- Actual epsilon scaling fixes the canonical split lift. -/
lemma scale_splitLiftClass (c : k) :
    scaleOrdinaryLiftClass f M c (splitLiftClass f M) =
      splitLiftClass f M := by
  apply Subtype.ext
  exact LineBundle.pullbackHom_comp_eq preservation (scale f c) (projection f)
    (scale_projection f c) _

/-- Actual pullback acts on pointed classes through the ordinary-class bijection. -/
def pointedScaleClass (c : k) (q : PointedDeformationClasses f M) :
    PointedDeformationClasses f M :=
  (pointedClassEquiv f M preservation).symm
    (scaleOrdinaryLiftClass f M c (pointedClassEquiv f M preservation q))

lemma pointedScaleClass_ordinary_val (c : k) (q : PointedDeformationClasses f M) :
    (pointedClassEquiv f M preservation (pointedScaleClass f M c q)).val =
      LineBundle.pullbackHom preservation (scale f c)
        (pointedClassEquiv f M preservation q).val := by
  exact congrArg Subtype.val ((pointedClassEquiv f M preservation).apply_symm_apply _)

lemma pointedTangentEquiv_pointedScaleClass (c : k) (q : PointedDeformationClasses f M) :
    pointedTangentEquiv f M (pointedScaleClass f M c q) =
      c • pointedTangentEquiv f M q := by
  apply Additive.ofMul.symm.injective
  apply Subtype.ext
  change (pointedTangentEquiv f M (pointedScaleClass f M c q)).toMul.val =
    LineBundle.pullbackHom preservation (scale f c)
      (pointedTangentEquiv f M q).toMul.val
  rw [pointedTangentEquiv_val, pointedScaleClass_ordinary_val]
  change _ = LineBundle.pullbackHom preservation (scale f c)
    ((pointedClassEquiv f M preservation q).val *
      (splitLiftClass f M).val⁻¹)
  rw [map_mul, map_inv]
  congr 2
  exact (congrArg Subtype.val (scale_splitLiftClass f M c)).symm

/-- Scalar multiplication is actual epsilon-scaling pullback on lift classes. -/
instance pointedClassesSMul : SMul k (PointedDeformationClasses f M) where
  smul := pointedScaleClass f M

lemma smul_pointedClasses_ordinary_val (c : k) (q : PointedDeformationClasses f M) :
    (pointedClassEquiv f M preservation (c • q)).val =
      LineBundle.pullbackHom preservation (scale f c)
        (pointedClassEquiv f M preservation q).val :=
  pointedScaleClass_ordinary_val f M c q

section SeparatedQuasiCompact

variable [IsSeparated f] [QuasiCompact f]

/-- The intrinsic tensor and scaling operations form a field module at every bundle. -/
instance pointedClassesModule : Module k (PointedDeformationClasses f M) :=
  Function.Injective.module k (pointedTangentAddEquiv f M).toAddMonoidHom
    (pointedTangentAddEquiv f M).injective
    (pointedTangentEquiv_pointedScaleClass f M)

/-- The normalized actual pointed tangent module is the previously computed deformation module. -/
def pointedTangentLinearEquiv :
    PointedDeformationClasses f M ≃ₗ[k] Additive (DeformationClasses preservation f) :=
  { pointedTangentAddEquiv f M with
    map_smul' := pointedTangentEquiv_pointedScaleClass f M }

/-- At every bundle, the actual pointed tangent module is structure-sheaf H¹. -/
def pointedTangentH1LinearEquiv (𝒰 : X.OrderedAffineCover) :
    PointedDeformationClasses f M ≃ₗ[k]
      (DerivedSections.relativeCohomology f 1).obj (structureSheaf X) :=
  (pointedTangentLinearEquiv f M).trans
    (deformationH1LinearEquiv preservation f 𝒰)

/-- The tangent dimension at any bundle equals the dimension of structure-sheaf H¹. -/
lemma finrank_pointedClasses (𝒰 : X.OrderedAffineCover) :
    Module.finrank k (PointedDeformationClasses f M) =
      Module.finrank k ((DerivedSections.relativeCohomology f 1).obj (structureSheaf X)) :=
  (pointedTangentH1LinearEquiv f M 𝒰).finrank_eq

end SeparatedQuasiCompact

/-- Properness makes actual pointed first-order classes finite at every bundle. -/
theorem finiteDimensional_pointedClasses [IsProper f] :
    FiniteDimensional k (PointedDeformationClasses f M) := by
  let := finiteDimensional_deformationClasses preservation f
  exact Module.Finite.equiv (pointedTangentLinearEquiv f M).symm

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
