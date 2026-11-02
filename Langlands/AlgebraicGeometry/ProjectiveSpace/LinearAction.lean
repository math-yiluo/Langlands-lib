import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearSubstitution

/-! # Actual scheme action of linear coordinate equivalences -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual projective-space morphism induced by a linear coordinate equivalence. -/
def linearAction (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    ProjectiveSpace R n ⟶ ProjectiveSpace R n :=
  Proj.map (gradedLinearSubstitution R n e.toLinearMap)
    (irrelevant_le_map_gradedLinearSubstitution R n e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem linearAction_refl :
    linearAction R n (LinearEquiv.refl R _) = 𝟙 (ProjectiveSpace R n) := by
  simpa only [ProjectiveSpace, linearAction, LinearEquiv.refl_toLinearMap,
    gradedLinearSubstitution_id] using
    (Proj.map_id (𝒜 := projectiveSpaceGrading R n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composition agrees with the covariant action on coordinate vectors. -/
theorem linearAction_comp
    (e f : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    linearAction R n e ≫ linearAction R n f = linearAction R n (e.trans f) := by
  simpa only [ProjectiveSpace, linearAction, gradedLinearSubstitution_comp,
    LinearEquiv.coe_trans] using
    (Proj.map_comp (gradedLinearSubstitution R n f.toLinearMap)
      (gradedLinearSubstitution R n e.toLinearMap)
      (irrelevant_le_map_gradedLinearSubstitution R n f)
      (irrelevant_le_map_gradedLinearSubstitution R n e)).symm

/-- An invertible coordinate change gives an actual scheme isomorphism. -/
def linearActionIso (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    ProjectiveSpace R n ≅ ProjectiveSpace R n where
  hom := linearAction R n e
  inv := linearAction R n e.symm
  hom_inv_id := by rw [linearAction_comp, LinearEquiv.self_trans_symm, linearAction_refl]
  inv_hom_id := by rw [linearAction_comp, LinearEquiv.symm_trans_self, linearAction_refl]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual linear action is over the coefficient-ring spectrum. -/
theorem linearAction_comp_toSpec
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    linearAction R n e ≫ projectiveSpaceToSpec R n = projectiveSpaceToSpec R n := by
  refine (Proj.mapAffineOpenCover (gradedLinearSubstitution R n e.toLinearMap)
    (irrelevant_le_map_gradedLinearSubstitution R n e)).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    linearAction, projectiveSpaceToSpec,
    Proj.awayι_comp_map_assoc (gradedLinearSubstitution R n e.toLinearMap) _ s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext r
  simp [Away.map, HomogeneousLocalization.map_mk, fromZeroRingHom,
    gradedLinearSubstitution_apply, projectiveSpaceConstants]

/-- The scheme action pulls homogeneous primes back by the actual polynomial substitution. -/
theorem linearAction_mem_iff
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (p : ProjectiveSpace R n) (x : ProjectiveCoordinateRing R n) :
    x ∈ (linearAction R n e p).asHomogeneousIdeal ↔
      linearSubstitution R n e.toLinearMap x ∈ p.asHomogeneousIdeal := Iff.rfl

/-- Actual linear incidence transforms by composition of the coordinate functional. -/
theorem linearAction_linearForm_mem_iff
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (p : ProjectiveSpace R n) (ℓ : (Fin (n + 1) → R) →ₗ[R] R) :
    (linearFormPolynomialEquiv R n ℓ : ProjectiveCoordinateRing R n) ∈
      (linearAction R n e p).asHomogeneousIdeal ↔
    (linearFormPolynomialEquiv R n (ℓ.comp e.toLinearMap) : ProjectiveCoordinateRing R n) ∈
      p.asHomogeneousIdeal := by
  rw [linearAction_mem_iff, linearSubstitution_linearForm]


/-- A scalar coordinate substitution multiplies a homogeneous polynomial by its degree power. -/
theorem linearSubstitution_smul_id_homogeneous (a : R) {d : ℕ}
    {x : ProjectiveCoordinateRing R n} (hx : x ∈ projectiveSpaceGrading R n d) :
    linearSubstitution R n (a • LinearMap.id) x = a ^ d • x := by
  classical
  have hX (i : Fin (n + 1)) :
      linearSubstitution R n (a • LinearMap.id) (MvPolynomial.X i) =
        a • MvPolynomial.X i := by
    rw [linearSubstitution_X]
    have hproj : (LinearMap.proj i : (Fin (n + 1) → R) →ₗ[R] R).comp
        (a • LinearMap.id) =
        a • (LinearMap.proj i : (Fin (n + 1) → R) →ₗ[R] R) := by
      ext v
      simp
    rw [hproj, map_smul, Submodule.coe_smul, linearFormPolynomialEquiv_proj]
  induction hx using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, smul_add]
  | monomial m r hm =>
    rw [MvPolynomial.monomial_eq]
    simp only [Finsupp.prod, map_mul, linearSubstitution_C, map_prod, map_pow, hX,
      smul_pow, Finset.prod_smul, Finset.prod_pow_eq_pow_sum]
    have hm' : ∑ i ∈ m.support, m i = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hm
    rw [hm']
    exact mul_smul_comm _ _ _

theorem smulOfUnit_toLinearMap (a : Rˣ) :
    (LinearEquiv.smulOfUnit a : (Fin (n + 1) → R) ≃ₗ[R] _).toLinearMap =
      (a : R) • LinearMap.id := by
  ext v i
  rfl

/-- Scalar units fix every actual point of projective space. -/
theorem linearAction_smulOfUnit_apply (a : Rˣ) (p : ProjectiveSpace R n) :
    linearAction R n (LinearEquiv.smulOfUnit a) p = p := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d x hx
  change linearSubstitution R n
    (LinearEquiv.smulOfUnit a : (Fin (n + 1) → R) ≃ₗ[R] _).toLinearMap x ∈
      p.asHomogeneousIdeal ↔ x ∈ p.asHomogeneousIdeal
  rw [smulOfUnit_toLinearMap, linearSubstitution_smul_id_homogeneous R n (a : R) hx,
    MvPolynomial.smul_eq_C_mul]
  exact Ideal.unit_mul_mem_iff_mem p.asHomogeneousIdeal.toIdeal
    (((a.isUnit.pow d).map MvPolynomial.C))

/-- Equal-degree fractions are unchanged by a scalar substitution whenever it is defined. -/
theorem homogeneousLocalization_scalar_map (a : R)
    (P : Submonoid (ProjectiveCoordinateRing R n))
    (h : P ≤ P.comap (gradedLinearSubstitution R n (a • LinearMap.id))) :
    HomogeneousLocalization.map (gradedLinearSubstitution R n (a • LinearMap.id)) h =
      RingHom.id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := z.mk_surjective
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    RingHom.id_apply, gradedLinearSubstitution_apply]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  change (c.den : ProjectiveCoordinateRing R n) *
      linearSubstitution R n (a • LinearMap.id) c.num =
    linearSubstitution R n (a • LinearMap.id) c.den * (c.num : ProjectiveCoordinateRing R n)
  rw [linearSubstitution_smul_id_homogeneous R n a c.num.2,
    linearSubstitution_smul_id_homogeneous R n a c.den.2]
  simp only [MvPolynomial.smul_eq_C_mul, mul_left_comm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar units act as the identity on the actual projective scheme, including its sheaf. -/
theorem linearAction_smulOfUnit (a : Rˣ) :
    linearAction R n (LinearEquiv.smulOfUnit a) = 𝟙 (ProjectiveSpace R n) := by
  have hb : (linearAction R n (LinearEquiv.smulOfUnit a)).base =
      (𝟙 (ProjectiveSpace R n) : ProjectiveSpace R n ⟶ _).base := by
    ext p
    exact linearAction_smulOfUnit_apply R n a p
  refine Scheme.Hom.ext hb ?_
  intro U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply Subtype.ext
  funext p
  change (Proj.comapStructureSheafFun
    (gradedLinearSubstitution R n (LinearEquiv.smulOfUnit a).toLinearMap) _
    U U (fun q hq => by
      change linearAction R n (LinearEquiv.smulOfUnit a) q ∈ U
      rw [linearAction_smulOfUnit_apply]
      exact hq) s.1) ⟨p.1, p.2⟩ =
        s.1 ⟨p.1, p.2⟩
  dsimp only [Proj.comapStructureSheafFun]
  have hs (q : ProjectiveSpace R n) (hq : q = p.1)
      (hI : q.asHomogeneousIdeal.toIdeal =
        p.1.asHomogeneousIdeal.toIdeal.comap
          (gradedLinearSubstitution R n (LinearEquiv.smulOfUnit a).toLinearMap))
      (hqU : q ∈ U) :
      localRingHom (gradedLinearSubstitution R n (LinearEquiv.smulOfUnit a).toLinearMap)
        q.asHomogeneousIdeal.toIdeal p.1.asHomogeneousIdeal.toIdeal hI
        (s.1 ⟨q, hqU⟩) = s.1 ⟨p.1, p.2⟩ := by
    subst q
    simp only [localRingHom, smulOfUnit_toLinearMap, homogeneousLocalization_scalar_map,
      RingHom.id_apply]
  exact hs _ (linearAction_smulOfUnit_apply R n a p.1) rfl _

end Langlands.AlgebraicGeometry.ProjectiveSpace
