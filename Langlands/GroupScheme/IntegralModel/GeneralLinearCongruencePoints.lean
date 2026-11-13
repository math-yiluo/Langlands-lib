import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.CongruenceTower

/-! # Matrices in the actual standard general linear congruence subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Matrix

namespace Langlands.GroupScheme.GeneralLinear

section Coefficients

variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

/-- Restriction of an actual general linear section applies the coefficient map
entry by entry, under the supplied standard base-change identification. -/
theorem rationalPointsEquiv_baseChangeSectionHom (f : R →+* A)
    (x : rationalPoints (groupScheme (Fin n) (CommRingCat.of R))) :
    rationalPointsEquiv n (CommRingCat.of A)
        (rationalPoints.map (baseChangeIso (Fin n)
          (Spec.map (CommRingCat.ofHom f))).hom
          (baseChangeSectionHom (Spec.map (CommRingCat.ofHom f))
            (groupScheme (Fin n) (CommRingCat.of R)) x)) =
      Matrix.GeneralLinearGroup.map f (rationalPointsEquiv n (CommRingCat.of R) x) := by
  apply Units.ext
  ext i j
  rw [rationalPointsEquiv_apply_apply, Matrix.GeneralLinearGroup.map_apply,
    rationalPointsEquiv_apply_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((baseChangeSectionHom (Spec.map (CommRingCat.ofHom f))
        (groupScheme (Fin n) (CommRingCat.of R)) x ≫
        (baseChangeIso (Fin n) (Spec.map (CommRingCat.ofHom f))).hom.hom.hom).left.appTop
          (entrySection (Fin n) (CommRingCat.of A) i j)) = _
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    (x.left.appTop (entrySection (Fin n) (CommRingCat.of R) i j))
  simp only [CategoryTheory.comp_apply] at hnat
  rw [baseChangeIso_hom_entry, baseChangeSectionHom_fst, Scheme.Hom.comp_appTop,
    CategoryTheory.comp_apply]
  exact hnat

end Coefficients

section Standard

variable (R K : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

set_option synthInstance.maxHeartbeats 100000 in
/-- Congruence of a standard integral section is exactly congruence of all
entries of its actual matrix. -/
theorem mem_standardIntegralModel_congruenceKernelAt_iff (k : ℕ+)
    (x : rationalPoints (groupScheme (Fin n) (CommRingCat.of R))) :
    x ∈ (standardIntegralModel R K (Fin n)).congruenceKernelAt k ↔
      ∀ i j, (rationalPointsEquiv n (CommRingCat.of R) x : Matrix (Fin n) (Fin n) R) i j -
        (1 : Matrix (Fin n) (Fin n) R) i j ∈ (IsLocalRing.maximalIdeal R) ^ (k : ℕ) := by
  let M := standardIntegralModel R K (Fin n)
  let f := IntegralModel.congruenceQuotient R k
  let e : rationalPoints (M.congruenceFibre k) ≃*
      GL (Fin n) (IntegralModel.congruenceRing R k) := (isoPointsEquiv (baseChangeIso (Fin n)
    (IntegralModel.congruenceBaseMap R k)) (Over.mk (𝟙 _))).trans
      (rationalPointsEquiv n (CommRingCat.of (IntegralModel.congruenceRing R k)))
  have he (y : M.integralSections) :
      e (M.reductionAt k y) =
        Matrix.GeneralLinearGroup.map f (rationalPointsEquiv n (CommRingCat.of R) y) :=
    rationalPointsEquiv_baseChangeSectionHom f y
  rw [IntegralModel.mem_congruenceKernelAt]
  constructor
  · intro hx i j
    have h := congrArg (fun z => (e z : Matrix (Fin n) (Fin n)
      (IntegralModel.congruenceRing R k)) i j) hx
    rw [he, map_one] at h
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (by
      simpa only [Matrix.GeneralLinearGroup.map_apply, Units.val_one, Matrix.one_apply,
        IntegralModel.congruenceQuotient, f, apply_ite, map_one, map_zero] using h)
  · intro hx
    apply e.injective
    rw [he, map_one]
    apply Units.ext
    ext i j
    have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hx i j)
    simpa only [Matrix.GeneralLinearGroup.map_apply, Units.val_one, Matrix.one_apply,
      IntegralModel.congruenceQuotient, f, apply_ite, map_one, map_zero] using h

/-- An actual matrix over the integral base that is congruent to the identity
supplies a point of the original generic congruence subgroup. -/
def standardCongruencePoint (k : ℕ+) (A : GL (Fin n) R)
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) R) i j -
      (1 : Matrix (Fin n) (Fin n) R) i j ∈ (IsLocalRing.maximalIdeal R) ^ (k : ℕ)) :
    (standardIntegralModel R K (Fin n)).congruenceSubgroupAt k :=
  ⟨(standardIntegralModel R K (Fin n)).integralPointMap
      ((rationalPointsEquiv n (CommRingCat.of R)).symm A),
    ⟨(rationalPointsEquiv n (CommRingCat.of R)).symm A,
      (mem_standardIntegralModel_congruenceKernelAt_iff R K k _).mpr
        (by simpa only [MulEquiv.apply_symm_apply] using hA), rfl⟩⟩

@[simp] theorem standardCongruencePoint_matrix (k : ℕ+) (A : GL (Fin n) R)
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) R) i j -
      (1 : Matrix (Fin n) (Fin n) R) i j ∈ (IsLocalRing.maximalIdeal R) ^ (k : ℕ)) :
    rationalPointsEquiv n (CommRingCat.of K) (standardCongruencePoint R K k A hA) =
      Matrix.GeneralLinearGroup.map (algebraMap R K) A := by
  change rationalPointsEquiv n (CommRingCat.of K)
    ((standardIntegralModel R K (Fin n)).integralPointMap
      ((rationalPointsEquiv n (CommRingCat.of R)).symm A)) = _
  rw [standardIntegralModel_integralPointMap, MulEquiv.apply_symm_apply]

end Standard

end Langlands.GroupScheme.GeneralLinear
