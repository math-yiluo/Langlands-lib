import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice

/-! # Integral points of the standard general linear integral model -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

section BaseChange

variable {n : Type} [Fintype n] [DecidableEq n] {R R' : CommRingCat.{u}}
  (b : Spec R' ⟶ Spec R)

set_option maxHeartbeats 400000 in
/-- The `(i, j)` coordinate of a point of the base change of `GL_{n,R}`, read through the
Library's identification with `GL_{n,R'}`, is the `(i, j)` coordinate of its projection
to `GL_{n,R}`. -/
theorem baseChangeIso_hom_entry {T : Over (Spec R')}
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme n R)).X) (i j : n) :
    (x ≫ (baseChangeIso n b).hom.hom.hom).left.appTop (entrySection n R' i j) =
      (x.left ≫ pullback.fst _ b).appTop (entrySection n R i j) := by
  have h := pointsEquiv_comp_baseChangeIso_hom (n := n) b x
  rw [← pointsEquiv_apply_apply, h, pointsEquiv_apply_apply]
  rfl

end BaseChange

section Standard

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] {N : ℕ}

/-- The matrix of the generic point of an integral section of the standard model is the
image under `algebraMap R K` of the matrix of the integral section. -/
theorem standardIntegralModel_integralPointMap
    (x : rationalPoints (groupScheme (Fin N) (CommRingCat.of R))) :
    rationalPointsEquiv N (CommRingCat.of K)
        ((standardIntegralModel R K (Fin N)).integralPointMap x) =
      Matrix.GeneralLinearGroup.map (algebraMap R K)
        (rationalPointsEquiv N (CommRingCat.of R) x) := by
  apply Units.ext
  ext i j
  rw [rationalPointsEquiv_apply_apply, Matrix.GeneralLinearGroup.map_apply,
    rationalPointsEquiv_apply_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((baseChangeSectionHom (Spec.algebraMap R K) (groupScheme (Fin N) (CommRingCat.of R)) x ≫
        (baseChangeIso (Fin N) (Spec.algebraMap R K)).hom.hom.hom).left.appTop
          (entrySection (Fin N) (CommRingCat.of K) i j)) = _
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
    (x.left.appTop (entrySection (Fin N) (CommRingCat.of R) i j))
  simp only [CategoryTheory.comp_apply] at hnat
  rw [baseChangeIso_hom_entry, baseChangeSectionHom_fst, Scheme.Hom.comp_appTop,
    CategoryTheory.comp_apply]
  exact hnat

/-- **Integral points of the standard model.** A rational point of `GL_n` over the fraction
field is an integral point of the standard model exactly when its matrix lies in the image of
`GL_n(R)`. -/
theorem mem_standardIntegralModel_integralPoints_iff
    (g : rationalPoints (groupScheme (Fin N) (CommRingCat.of K))) :
    g ∈ (standardIntegralModel R K (Fin N)).integralPoints ↔
      rationalPointsEquiv N (CommRingCat.of K) g ∈
        (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap R K)).range := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (standardIntegralModel_integralPointMap R K x).symm⟩
  · rintro ⟨C, hC⟩
    refine ⟨(rationalPointsEquiv N (CommRingCat.of R)).symm C, ?_⟩
    apply (rationalPointsEquiv N (CommRingCat.of K)).injective
    rw [standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply, hC]

end Standard

end Langlands.GroupScheme.GeneralLinear
