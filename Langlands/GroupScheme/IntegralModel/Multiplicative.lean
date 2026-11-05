import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.MultiplicativeGeometry

/-! # The canonical smooth integral model of the multiplicative group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual multiplicative group is affine over every base scheme. -/
theorem isAffineHom_gm (S : Scheme.{u}) : IsAffineHom (Gm S).X.hom := by
  have : IsAffineHom Gm.overSpecZ.{u}.hom := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    infer_instance
  change IsAffineHom (pullback.snd Gm.overSpecZ.hom (Gm.toSpecZ S))
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom Gm.overSpecZ.hom›

namespace IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The actual multiplicative group over `R`, with its canonical generic identification. -/
def multiplicative : IntegralModel R K (Gm (Spec (CommRingCat.of K))).toGrp where
  group := (Gm (Spec (CommRingCat.of R))).toGrp
  affine := isAffineHom_gm _
  flat := by
    have := smooth_gm (Spec (CommRingCat.of R))
    infer_instance
  finiteType := by
    have := smooth_gm (Spec (CommRingCat.of R))
    infer_instance
  genericIso := Gm.baseChangeIso (Spec.algebraMap R K)

/-- This canonical model is smooth over the actual integral base. -/
theorem multiplicative_isSmooth : (multiplicative R K).IsSmooth :=
  smooth_gm (Spec (CommRingCat.of R))

/-- Its integral sections are exactly the units of the supplied coefficient ring. -/
def multiplicativeSectionsEquiv : (multiplicative R K).integralSections ≃* Rˣ :=
  Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of R)))

/-- The canonical generic identification sends the integral section to the same scalar unit. -/
theorem multiplicative_integralPointMap (x : (multiplicative R K).integralSections) :
    Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))
        ((multiplicative R K).integralPointMap x) =
      Units.map (algebraMap R K).toMonoidHom (multiplicativeSectionsEquiv R K x) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (Gm.pointsEquiv _ _
        (baseChangeSectionHom (Spec.algebraMap R K)
          (Gm (Spec (CommRingCat.of R))).toGrp x ≫
            (Gm.baseChangeIso (Spec.algebraMap R K)).hom.hom.hom)).val = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply]
  change (Gm.affinePointsEquiv (Spec.algebraMap R K)
      (baseChangeBasePointsEquiv (Spec.algebraMap R K)
        (Gm (Spec (CommRingCat.of R))).toGrp
        (baseChangeSectionHom (Spec.algebraMap R K)
          (Gm (Spec (CommRingCat.of R))).toGrp x)) : K) = _
  change (Gm.affinePointsEquiv (Spec.algebraMap R K)
      ((baseChangeBasePointsEquiv (Spec.algebraMap R K)
        (Gm (Spec (CommRingCat.of R))).toGrp)
        ((baseChangeBasePointsEquiv (Spec.algebraMap R K)
          (Gm (Spec (CommRingCat.of R))).toGrp).symm
          ((Over.homMk (Spec.algebraMap R K) (by simp) :
            Over.mk (Spec.algebraMap R K) ⟶
              Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ x))) : K) = _
  rw [MulEquiv.apply_symm_apply]
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((Spec.algebraMap R K).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom) _ =
    (algebraMap R K) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

end IntegralModel
end Langlands.GroupScheme
