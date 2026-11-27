import Langlands.Geometry.Analytic.GroundFieldChangingCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientAction
import Mathlib.CategoryTheory.Endomorphism

/-! # Analytic coefficient automorphisms of scalar-extended spaces -/

noncomputable section

universe u v

namespace Langlands.Analytic

open _root_.CategoryTheory CategoryTheory.Functor Opposite CompleteUltrametricField
open PresentedAffinoidAlgebra.GroundFieldExtension

namespace SpaceOverField

variable {K L : CompleteUltrametricField.{u}}

/-- Isometric automorphisms of the extension field fixing the image of the given embedding. -/
abbrev CoefficientAutomorphisms (e : K ⟶ L) :=
  letI := e.normedAlgebra
  isometricAutomorphisms K L

/-- The underlying field arrow of an isometric coefficient automorphism. -/
def coefficientFieldMap {e : K ⟶ L} (σ : CoefficientAutomorphisms e) : L ⟶ L :=
  ⟨σ.val.toRingHom, σ.property⟩

@[simp]
theorem coefficientFieldMap_apply {e : K ⟶ L} (σ : CoefficientAutomorphisms e) (a : L) :
    coefficientFieldMap σ a = σ.val a :=
  rfl

@[simp]
theorem coefficientFieldMap_one (e : K ⟶ L) :
    coefficientFieldMap (1 : CoefficientAutomorphisms e) = 𝟙 L :=
  CompleteUltrametricField.Hom.ext rfl

theorem coefficientFieldMap_mul {e : K ⟶ L} (σ τ : CoefficientAutomorphisms e) :
    coefficientFieldMap (σ * τ) = coefficientFieldMap τ ≫ coefficientFieldMap σ :=
  CompleteUltrametricField.Hom.ext rfl

theorem comp_coefficientFieldMap {e : K ⟶ L} (σ : CoefficientAutomorphisms e) :
    e ≫ coefficientFieldMap σ = e := by
  let := e.normedAlgebra
  apply CompleteUltrametricField.Hom.ext
  ext a
  exact σ.val.commutes a

variable (e : K ⟶ L) (X : K.CompatibleAnalyticCategory.{u, v})

/-- The extension of an analytic space, regarded as an object over its new field. -/
abbrev scalarExtendedSpace : SpaceOverField.{u, v} :=
  withField L ((localizedExtend e).obj X)

private abbrev p : scalarExtendedSpace e X ⟶ withField K X :=
  scalarExtensionArrow (withField K X) e

private instance :
    fieldProjection.IsStronglyCartesian e.op (p e X) :=
  scalarExtensionArrow_isStronglyCartesian (withField K X) e

/-- The map over the inverse coefficient embedding is the actual tower comparison,
transported along the fact that the embedding fixes the ground field. -/
def coefficientLiftMap (σ : CoefficientAutomorphisms e) :
    (localizedExtend e).obj X ⟶ (localizedExtend (coefficientFieldMap σ⁻¹)).obj ((localizedExtend e).obj X) :=
  eqToHom (congrArg (fun d => (localizedExtend.{u, v} d).obj X)
    (comp_coefficientFieldMap σ⁻¹).symm) ≫
    (localizedExtendComp e (coefficientFieldMap σ⁻¹)).hom.app X

/-- The lift of a coefficient automorphism on the scalar-extended space.
The inverse automorphism is used on pullbacks, so that the lifts act on the left. -/
def coefficientLift (σ : CoefficientAutomorphisms e) :
    scalarExtendedSpace e X ⟶ scalarExtendedSpace e X :=
  IsStronglyCartesian.map fieldProjection e.op (p e X)
    (g := (coefficientFieldMap σ⁻¹).op)
    (congrArg Quiver.Hom.op (comp_coefficientFieldMap σ⁻¹).symm) (p e X)

@[simp]
theorem coefficientLift_comp_projection (σ : CoefficientAutomorphisms e) :
    coefficientLift e X σ ≫ p e X = p e X :=
  IsStronglyCartesian.fac _ _ _ _ _

private instance coefficientLift_isHomLift (σ : CoefficientAutomorphisms e) :
    fieldProjection.IsHomLift (coefficientFieldMap σ⁻¹).op (coefficientLift e X σ) :=
  IsStronglyCartesian.map_isHomLift _ _ _ _ _

theorem coefficientLift_eq_homMk (σ : CoefficientAutomorphisms e) :
    coefficientLift e X σ = homMk (coefficientFieldMap σ⁻¹) (coefficientLiftMap e X σ) := by
  let d := coefficientFieldMap σ⁻¹
  let q : scalarExtendedSpace e X ⟶ scalarExtendedSpace e X := homMk d (coefficientLiftMap e X σ)
  let : fieldProjection.IsHomLift d.op q := IsHomLift.map fieldProjection q
  have hf : q ≫ p e X = p e X := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
      (congrArg Quiver.Hom.op (comp_coefficientFieldMap σ⁻¹)) ?_
    let a := (localizedExtendComp e d).app X
    let k := eqToHom (congrArg (fun f => (localizedExtend.{u, v} f).obj X)
      (comp_coefficientFieldMap σ⁻¹).symm)
    change (k ≫ a.hom) ≫ (localizedExtend d).map (𝟙 _) ≫ a.inv = 𝟙 _ ≫ eqToHom _
    calc
      _ = (k ≫ a.hom) ≫ a.inv :=
        congrArg ((k ≫ a.hom) ≫ ·)
          ((congrArg (· ≫ a.inv) ((localizedExtend d).map_id _)).trans (Category.id_comp _))
      _ = k := (Category.assoc _ _ _).trans
        ((congrArg (k ≫ ·) a.hom_inv_id).trans (Category.comp_id _))
      _ = _ := (Category.id_comp _).symm
  have hd : e.op = d.op ≫ e.op := congrArg Quiver.Hom.op (comp_coefficientFieldMap σ⁻¹).symm
  exact (IsStronglyCartesian.map_uniq fieldProjection e.op (p e X) (g := d.op) hd (p e X) q hf).symm

@[simp]
theorem fieldMap_coefficientLift (σ : CoefficientAutomorphisms e) :
    fieldMap (coefficientLift e X σ) = coefficientFieldMap σ⁻¹ :=
  congrArg Quiver.Hom.unop (IsHomLift.fac fieldProjection (coefficientFieldMap σ⁻¹).op
    (coefficientLift e X σ)).symm

@[simp]
theorem coefficientLift_one : coefficientLift e X 1 = 𝟙 _ := by
  let : fieldProjection.IsHomLift (𝟙 (op L)) (coefficientLift e X 1) := by
    simpa only [inv_one, coefficientFieldMap_one, op_id] using
      (coefficientLift_isHomLift e X (1 : CoefficientAutomorphisms e))
  let : fieldProjection.IsHomLift (𝟙 (op L)) (𝟙 (scalarExtendedSpace e X)) := IsHomLift.id rfl
  exact IsStronglyCartesian.ext fieldProjection e.op (p e X) (𝟙 (op L))
    ((coefficientLift_comp_projection e X 1).trans (Category.id_comp _).symm)

theorem coefficientLift_mul (σ τ : CoefficientAutomorphisms e) :
    coefficientLift e X (σ * τ) = coefficientLift e X τ ≫ coefficientLift e X σ := by
  let : fieldProjection.IsHomLift ((coefficientFieldMap (σ * τ)⁻¹).op)
      (coefficientLift e X τ ≫ coefficientLift e X σ) := by
    rw [mul_inv_rev, coefficientFieldMap_mul, op_comp]
    infer_instance
  apply IsStronglyCartesian.ext fieldProjection e.op (p e X) (coefficientFieldMap (σ * τ)⁻¹).op
  simp only [Category.assoc, coefficientLift_comp_projection]

private def coefficientIso (σ : CoefficientAutomorphisms e) : scalarExtendedSpace e X ≅ scalarExtendedSpace e X where
  hom := coefficientLift e X σ
  inv := coefficientLift e X σ⁻¹
  hom_inv_id := (coefficientLift_mul e X σ⁻¹ σ).symm.trans (by rw [inv_mul_cancel, coefficientLift_one])
  inv_hom_id := (coefficientLift_mul e X σ σ⁻¹).symm.trans (by rw [mul_inv_cancel, coefficientLift_one])

/-- The actual action by semilinear analytic automorphisms on scalar extension. -/
def coefficientAnalyticAction : CoefficientAutomorphisms e →* Aut (scalarExtendedSpace e X) where
  toFun σ := Aut.of (coefficientIso e X σ)
  map_one' := Aut.ext (Iso.ext (coefficientLift_one e X))
  map_mul' σ τ := Aut.ext (Iso.ext (coefficientLift_mul e X σ τ))

@[simp]
theorem coefficientAnalyticAction_hom (σ : CoefficientAutomorphisms e) :
    (coefficientAnalyticAction e X σ).asIso.hom = coefficientLift e X σ :=
  rfl

end SpaceOverField

end Langlands.Analytic
