import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.LinearActionBaseChange

/-! # Restriction of actual projective coordinate lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K R B : Type u} [CommRing K] [CommRing R] [CommRing B] (n : ℕ)

/-- Unit-chart evaluation commutes with a map of target rings. -/
theorem unitChartRingMap_target_comp
    (f : ProjectiveCoordinateRing R n →+* B) (φ : B →+* K)
    (t : ProjectiveCoordinateRing R n) (ht : IsUnit (f t)) :
    unitChartRingMap n (φ.comp f) t (ht.map φ) =
      φ.comp (unitChartRingMap n f t ht) := by
  have h : Localization.awayLift (φ.comp f) t (ht.map φ) =
      φ.comp (Localization.awayLift f t ht) := by
    apply IsLocalization.ringHom_ext (M := .powers t)
    simp only [RingHom.comp_assoc, Localization.awayLift, IsLocalization.Away.lift_comp]
  unfold unitChartRingMap
  rw [h, RingHom.comp_assoc]

/-- Chart evaluation commutes with graded substitution between coefficient rings. -/
theorem chartRingMap_comp_coefficients
    (g : projectiveSpaceGrading K n →+*ᵍ projectiveSpaceGrading R n)
    (f : ProjectiveCoordinateRing R n →+* B) (t : ProjectiveCoordinateRing K n) :
    chartRingMap n (f.comp g.toRingHom) t =
      (chartRingMap n f (g t)).comp (Away.map g t) := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  change (IsLocalization.map (M := .powers t) (T := .powers (f (g t)))
      (Localization.Away (f (g t))) (f.comp g.toRingHom) (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
        exact le_rfl))
      (HomogeneousLocalization.val (.mk c)) =
    (IsLocalization.map (M := .powers (g t)) (T := .powers (f (g t)))
      (Localization.Away (f (g t))) f (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]))
      (HomogeneousLocalization.val (HomogeneousLocalization.map g (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]) (.mk c)))
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rfl

/-- Actual global-coordinate maps commute with graded coefficient restriction. -/
theorem fromOfGlobalSections_comp_coefficients {X : Scheme.{u}}
    (g : projectiveSpaceGrading K n →+*ᵍ projectiveSpaceGrading R n)
    (hg : HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).map g)
    (f : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n)).toIdeal.map f = ⊤)
    (hfg : (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).toIdeal.map
      (f.comp g.toRingHom) = ⊤) :
    Proj.fromOfGlobalSections (projectiveSpaceGrading K n) (f.comp g.toRingHom) hfg =
      Proj.fromOfGlobalSections (projectiveSpaceGrading R n) f hf ≫ Proj.map g hg := by
  apply (Proj.openCoverOfMapIrrelevantEqTop (projectiveSpaceGrading K n)
    (f.comp g.toRingHom) hfg).hom_ext
  rintro ⟨d, t, hd, ht⟩
  change (X.basicOpen ((f.comp g.toRingHom) t)).ι ≫ _ = _
  rw [basicOpen_ι_fromOfGlobalSections n _ _ hd t ht]
  change _ = (X.basicOpen (f (g t))).ι ≫ _
  rw [← Category.assoc, basicOpen_ι_fromOfGlobalSections n f hf hd (g t) (g.2 ht)]
  simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι]
  congr 1
  congr 1
  congr 1
  rw [Proj.awayι_comp_map g hg hd t ht]
  change Spec.map (CommRingCat.ofHom (chartRingMap n (f.comp g.toRingHom) t)) ≫ _ =
    Spec.map (CommRingCat.ofHom (chartRingMap n f (g t))) ≫
      Spec.map (CommRingCat.ofHom (Away.map g t)) ≫ _
  rw [chartRingMap_comp_coefficients, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]

end Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

open GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R K : Type u} [CommRing R] [CommRing K] (n : ℕ)
  {X Y : Scheme.{u}} [Algebra R Γ(X, ⊤)]

/-- The coordinate point has the expected coefficient structure morphism. -/
@[reassoc]
theorem basisPoint_toSpec (j : Fin (n + 1)) :
    basisPoint (R := R) n X j ≫ projectiveSpaceToSpec R n =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) := by
  unfold basisPoint projectiveSpaceToSpec
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact basisEval_C n X j r

/-- Coordinate points commute with arbitrary scheme-source maps whose
coefficient structures are compatible. -/
theorem comp_basisPoint [Algebra R Γ(Y, ⊤)] (a : Y ⟶ X)
    (hcoeff : a.appTop.hom.comp (algebraMap R Γ(X, ⊤)) = algebraMap R Γ(Y, ⊤))
    (j : Fin (n + 1)) :
    a ≫ basisPoint (R := R) n X j = basisPoint (R := R) n Y j := by
  have heval : a.appTop.hom.comp (basisEval (R := R) n X j) =
      basisEval (R := R) n Y j := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, basisEval_C] using DFunLike.congr_fun hcoeff r
    · intro i
      by_cases h : i = j
      · subst i
        simp
      · simp [h]
  rw [basisPoint, fromOfGlobalSections_eq_unitChart n _ _ Nat.one_pos
    (MvPolynomial.X j) (projectiveSpace_X_mem R n j) (by simp)]
  rw [basisPoint, fromOfGlobalSections_eq_unitChart n _ _ Nat.one_pos
    (MvPolynomial.X j) (projectiveSpace_X_mem R n j) (by simp)]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp_assoc]
  change Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (a.appTop.hom.comp
      (unitChartRingMap n (basisEval (R := R) n X j) (MvPolynomial.X j) (by simp)))) ≫ _ = _
  rw [← unitChartRingMap_target_comp]
  simp only [heval]

/-- Coordinate points commute with coefficient restriction under the specified
compatibility of the two coefficient structures on the source. -/
theorem basisPoint_coefficientMap [Algebra K Γ(X, ⊤)] (φ : K →+* R)
    (hcoeff : (algebraMap R Γ(X, ⊤)).comp φ = algebraMap K Γ(X, ⊤))
    (j : Fin (n + 1)) :
    basisPoint (R := R) n X j ≫ coefficientMap n φ =
      basisPoint (R := K) n X j := by
  let := φ.toAlgebra
  let g := ProjSpace.mvMapGraded K R n
  have heval : (basisEval (R := R) n X j).comp g.toRingHom =
      basisEval (R := K) n X j := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change basisEval (R := R) n X j (MvPolynomial.map φ (MvPolynomial.C r)) = _
      simpa only [MvPolynomial.map_C, basisEval_C, RingHom.comp_apply] using
        DFunLike.congr_fun hcoeff r
    · intro i
      change basisEval (R := R) n X j (MvPolynomial.map φ (MvPolynomial.X i)) = _
      simp
  have hfg : (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).toIdeal.map
      ((basisEval (R := R) n X j).comp g.toRingHom) = ⊤ := by
    rw [heval]
    exact basisEval_primitive n X j
  have h := fromOfGlobalSections_comp_coefficients n
    (show projectiveSpaceGrading K n →+*ᵍ projectiveSpaceGrading R n from g)
    (ProjSpace.irrelevant_le_map_mvMapGraded K R n)
    (basisEval (R := R) n X j) (basisEval_primitive n X j) hfg
  unfold basisPoint coefficientMap ProjSpace.map
  simpa only [heval] using h.symm

end Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines
