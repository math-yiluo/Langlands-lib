import Langlands.AlgebraicGeometry.Picard.ProjectiveGenericExtension
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionStatement

/-! # Actual self-product extension from affine projectivity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R)))

local instance : Smooth (mumfordProduct A).hom := by
  change Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

local instance : UniversallyClosed (mumfordProduct A).hom := by
  change UniversallyClosed (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

local instance : IsSeparated (mumfordProduct A).hom := by
  change IsSeparated (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

local instance : GeometricallyConnected (mumfordProduct A).hom := by
  change GeometricallyConnected (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  exact GeometricallyConnected.comp (pullback.fst A.X.hom A.X.hom) A.X.hom

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K] in
/-- The exact canonical self-product map is the generic pullback of the
actual total self-product structure morphism. -/
theorem isPullback_mumfordProduct_generic :
    let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let p := (mumfordProduct A).hom
    let e := mumfordProductBaseChangeIso A b
    IsPullback (mumfordProductBaseChangeMap A b)
      (e.hom ≫ pullback.snd p b) p b := by
  dsimp only
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := (mumfordProduct A).hom
  let e := mumfordProductBaseChangeIso A b
  apply IsPullback.of_iso_pullback _ e (mumfordProductBaseChangeIso_hom_fst A b) rfl
  constructor
  change mumfordProductBaseChangeMap A b ≫ p = (e.hom ≫ pullback.snd p b) ≫ b
  calc
    _ = (e.hom ≫ pullback.fst p b) ≫ p := by
      exact congrArg (fun f => f ≫ p) (mumfordProductBaseChangeIso_hom_fst A b).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f)
        (pullback.condition (f := p) (g := b))

omit [ValuationRing R] in
/-- Generic restriction along the target's canonical self-product map
is injective on the actual sections of every total open. -/
theorem mumfordProduct_generic_app_injective
    (U : (mumfordProduct A).left.Opens) :
    Function.Injective
      ((mumfordProductBaseChangeMap A
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app U) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let : IsSchemeTheoreticallyDominant b :=
    fractionFieldSpec_isSchemeTheoreticallyDominant K
  rw [← mumfordProductBaseChangeIso_hom_fst A b]
  exact Scheme.Hom.app_injective _ U

variable (hproj : AffineClosedFibreSectionProjectivity (mumfordProduct A).hom)
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left)

/-- An actual total self-product line bundle extending the given actual
generic self-product bundle, with affine section projectivity as input. -/
def mumfordProductLineBundleExtension : LineBundle (mumfordProduct A).left :=
  lineBundleOfClosedFibreFrames (mumfordProduct A).hom K
    (mumfordProductBaseChangeMap A (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    ((mumfordProductBaseChangeIso A
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).hom ≫ pullback.snd _ _)
    (isPullback_mumfordProduct_generic K A) hproj
    (mumfordProduct_generic_app_injective K A) D
    (mumfordProductClosedFibreGenericFrames K A D)

/-- The chosen total bundle restricts to the original generic bundle
under exactly the canonical self-product map in the target statement. -/
def mumfordProductLineBundleExtensionIso :
    ((LineBundle.pullback (mumfordProductBaseChangeMap A
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
        (mumfordProductLineBundleExtension K A hproj D)).obj ≅ D.obj :=
  closedFibreFramesIso (mumfordProduct A).hom K
    (mumfordProductBaseChangeMap A (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    ((mumfordProductBaseChangeIso A
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).hom ≫ pullback.snd _ _)
    (isPullback_mumfordProduct_generic K A) hproj
    (mumfordProduct_generic_app_injective K A) D
    (mumfordProductClosedFibreGenericFrames K A D)

omit R K A hproj D in
/-- Conditional assembly: the separate integral-fibre projectivity
proposition suffices for the exact published two-axis extension proposition. -/
theorem valuationRingTwoAxisExtension_of_integralFibreProjectivity
    (h : Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement.{u}) :
    ValuationRingTwoAxisExtensionStatement.{u} := by
  intro R _ _ _ K _ _ _ A
  dsimp only
  intro D _ _
  let hp := affineClosedFibreSectionProjectivity_of_integralFibreProjectivity
    (mumfordProduct A).hom h
  exact ⟨mumfordProductLineBundleExtension K A hp D,
    ⟨mumfordProductLineBundleExtensionIso K A hp D⟩⟩

end Langlands.AbelianScheme
