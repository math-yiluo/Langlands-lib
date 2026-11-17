import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Reductive.BaseChange

/-! # The integral model supplied by a reductive group over the base ring -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A reductive group over a domain is an integral model of its actual generic fibre. -/
def ofReductive (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G) :
    IntegralModel R K ((GroupScheme.baseChange (Spec.algebraMap R K)).obj G) := by
  let : Smooth G.X.hom := hG.smooth
  exact
    { group := G
      affine := hG.isAffineHom
      flat := inferInstance
      finiteType := inferInstance
      genericIso := Iso.refl _ }

variable (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)

/-- The canonical model's point map is the pullback of the original section. -/
theorem ofReductive_integralPointMap (y : rationalPoints G) :
    (ofReductive (K := K) G hG).integralPointMap y =
      baseChangeSectionHom (Spec.algebraMap R K) G y := by
  change baseChangeSectionHom (Spec.algebraMap R K) G y ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Reading the canonical model's generic point over the original base is restriction
of the integral section along `Spec K → Spec R`. -/
theorem ofReductive_integralPointMap_comparison (y : rationalPoints G) :
    baseChangeBasePointsEquiv (Spec.algebraMap R K) G
        ((ofReductive (K := K) G hG).integralPointMap y) =
      (Over.homMk (Spec.algebraMap R K) (by simp) :
        Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 _)) ≫ y := by
  rw [ofReductive_integralPointMap]
  exact (baseChangeBasePointsEquiv (Spec.algebraMap R K) G).apply_symm_apply _

/-- Integral-point membership for the canonical model is exactly the original
restriction-image condition under the pullback point equivalence. -/
theorem ofReductive_mem_integralPoints_iff
    (x : rationalPoints ((GroupScheme.baseChange (Spec.algebraMap R K)).obj G)) :
    x ∈ (ofReductive (K := K) G hG).integralPoints ↔
      ∃ y : rationalPoints G,
        baseChangeBasePointsEquiv (Spec.algebraMap R K) G x =
          (Over.homMk (Spec.algebraMap R K) (by simp) :
            Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 _)) ≫ y := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, ofReductive_integralPointMap_comparison G hG y⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (baseChangeBasePointsEquiv (Spec.algebraMap R K) G).injective ?_⟩
    rw [ofReductive_integralPointMap_comparison, hy]

/-- The inverse point correspondence turns a restricted point into a point of the
canonical integral model, and detects all such points. -/
theorem ofReductive_baseChangePoint_mem_integralPoints_iff
    (x : Over.mk (Spec.algebraMap R K) ⟶ G.X) :
    (baseChangeBasePointsEquiv (Spec.algebraMap R K) G).symm x ∈
        (ofReductive (K := K) G hG).integralPoints ↔
      ∃ y : rationalPoints G,
        x = (Over.homMk (Spec.algebraMap R K) (by simp) :
          Over.mk (Spec.algebraMap R K) ⟶ Over.mk (𝟙 _)) ≫ y := by
  rw [ofReductive_mem_integralPoints_iff, MulEquiv.apply_symm_apply]

/-- A homomorphism of reductive groups is a model homomorphism for their canonical
generic fibres. -/
def homOfReductive
    {H : GroupScheme (Spec (CommRingCat.of R))} (hH : IsReductive H) (q : G ⟶ H) :
    (ofReductive (K := K) G hG).Hom (ofReductive (K := K) H hH)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map q) where
  hom := q
  generic_comm := by
    simp [ofReductive]

end Langlands.GroupScheme.IntegralModel
