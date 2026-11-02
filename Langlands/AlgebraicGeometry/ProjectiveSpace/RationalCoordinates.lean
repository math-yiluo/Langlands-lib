import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearForms
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Normalized coordinates for actual projective-space points -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

local instance (j : Fin (n + 1)) :
    Algebra R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway R n j

/-- Divide an actual homogeneous linear polynomial by the chart coordinate. -/
def degreeOneDehomogenize (j : Fin (n + 1)) :
    projectiveSpaceGrading R n 1 →ₗ[R]
      Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) where
  toFun f := Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (_root_.AlgebraicGeometry.ProjSpace.X_mem_one R n j) 1 f
    (by simpa only [one_smul, projectiveSpaceGrading] using f.2)
  map_add' f g := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, val_add, Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r f := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, Submodule.coe_smul, RingHom.id_apply]
    simp only [Algebra.smul_def]
    rw [val_mul, _root_.AlgebraicGeometry.ProjSpace.val_algebraMap, Away.val_mk]
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp

@[simp]
theorem degreeOneDehomogenize_basis (j k : Fin (n + 1)) :
    degreeOneDehomogenize R n j (degreeOneBasis R n k) =
      _root_.AlgebraicGeometry.ProjSpace.ratio R n j k := by
  apply HomogeneousLocalization.val_injective
  simp [degreeOneDehomogenize, _root_.AlgebraicGeometry.ProjSpace.ratio]

theorem degreeOneDehomogenize_linearForm (j : Fin (n + 1))
    (ℓ : (Fin (n + 1) → R) →ₗ[R] R) :
    degreeOneDehomogenize R n j (linearFormPolynomialEquiv R n ℓ) =
      ∑ k, algebraMap R _ (ℓ (Pi.single k 1)) *
        _root_.AlgebraicGeometry.ProjSpace.ratio R n j k := by
  have hf : linearFormPolynomialEquiv R n ℓ =
      ∑ k, ℓ (Pi.single k 1) • degreeOneBasis R n k := by
    apply Subtype.ext
    simpa using linearFormPolynomialEquiv_coe R n ℓ
  rw [hf]
  simp [Algebra.smul_def]

variable {K : Type u} [Field K]

/-- Ratio values of a chart algebra map, with its selected coordinate normalized to one. -/
def chartCoordinates (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K) :
    Fin (n + 1) → K :=
  fun k => φ (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k)

@[simp]
theorem chartCoordinates_self (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K) :
    chartCoordinates n j φ j = 1 := by
  simp [chartCoordinates, _root_.AlgebraicGeometry.ProjSpace.ratio_self]

theorem chartCoordinates_ne_zero (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K) :
    chartCoordinates n j φ ≠ 0 := by
  intro h
  have := congrFun h j
  simp at this

@[simp]
theorem chartCoordinates_eval (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K) :
    φ (degreeOneDehomogenize K n j (linearFormPolynomialEquiv K n ℓ)) =
      ℓ (chartCoordinates n j φ) := by
  rw [degreeOneDehomogenize_linearForm]
  simp only [map_sum, map_mul, AlgHom.commutes]
  have h := congrArg ℓ ((Pi.basisFun K (Fin (n + 1))).sum_repr
    (chartCoordinates n j φ))
  simpa [map_sum, map_smul, Pi.basisFun_apply, mul_comm, chartCoordinates] using h

/-- The actual projective-space morphism obtained from an affine chart map. -/
def chartPoint (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K) :
    Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n :=
  Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)
      (_root_.AlgebraicGeometry.ProjSpace.X_mem_one K n j) Nat.one_pos

set_option backward.isDefEq.respectTransparency false in
theorem chartPoint_comp_toSpec (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K) :
    chartPoint n j φ ≫ projectiveSpaceToSpec K n = 𝟙 _ := by
  rw [chartPoint, Category.assoc, toSpec_eq_projSpace_π,
    _root_.AlgebraicGeometry.ProjSpace.awayι_comp_π, ← Spec.map_comp]
  apply (Spec.map_eq_id).mpr
  ext r
  exact φ.commutes r

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem chartPoint_preimage_linear_basicOpen (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K)
    (f : projectiveSpaceGrading K n 1) :
    chartPoint n j φ ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K n) (f : ProjectiveCoordinateRing K n) =
      PrimeSpectrum.basicOpen (φ (degreeOneDehomogenize K n j f)) := by
  have hf : (f : ProjectiveCoordinateRing K n) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1 := f.2
  have he : Away.isLocalizationElem
      (_root_.AlgebraicGeometry.ProjSpace.X_mem_one K n j) hf =
        degreeOneDehomogenize K n j f := by
    apply HomogeneousLocalization.val_injective
    simp [Away.isLocalizationElem, degreeOneDehomogenize]
  have hchart : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j) (_root_.AlgebraicGeometry.ProjSpace.X_mem_one K n j) Nat.one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) f =
        PrimeSpectrum.basicOpen (degreeOneDehomogenize K n j f) :=
    (Proj.awayι_preimage_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (_root_.AlgebraicGeometry.ProjSpace.X_mem_one K n j) Nat.one_pos hf Nat.one_pos).trans
        (congrArg PrimeSpectrum.basicOpen he)
  exact (Scheme.Hom.comp_preimage _ _ _).trans
    ((congrArg (fun U : (Spec (CommRingCat.of
      (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)))).Opens =>
        Spec.map (CommRingCat.ofHom φ.toRingHom) ⁻¹ᵁ U) hchart).trans
      (SpecMap_preimage_basicOpen _ _))

/-- Homogeneous-prime membership at the actual point is precisely linear vanishing. -/
theorem chartPoint_linearForm_mem_iff (j : Fin (n + 1))
    (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K) :
    (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
      (chartPoint n j φ (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
        ℓ (chartCoordinates n j φ) = 0 := by
  have h := congrArg (fun U : (Spec (CommRingCat.of K)).Opens =>
    IsLocalRing.closedPoint K ∈ U)
    (chartPoint_preimage_linear_basicOpen n j φ (linearFormPolynomialEquiv K n ℓ))
  change (¬ _ ) = (¬ _ ) at h
  simpa [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot] using
    not_iff_not.mp (Eq.to_iff h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual rational point over the coefficient field comes from a chart algebra map. -/
theorem exists_chartPoint (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    ∃ (j : Fin (n + 1))
      (φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X j) →ₐ[K] K), chartPoint n j φ = p := by
  have hcov : p (IsLocalRing.closedPoint K) ∈
      (⨆ j, projectiveSpaceCoordinateOpen K n j) := by
    rw [iSup_projectiveSpaceCoordinateOpen]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have htop : p ⁻¹ᵁ projectiveSpaceCoordinateOpen K n j = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff _).mp hj
  have hrange : Set.range p ⊆ Set.range ((affineOpenCover K n).openCover.f j) := by
    rintro x ⟨y, rfl⟩
    change p y ∈ ((affineOpenCover K n).openCover.f j).opensRange
    rw [affineOpenCover_opensRange]
    have hy : y ∈ p ⁻¹ᵁ projectiveSpaceCoordinateOpen K n j := by
      rw [htop]
      trivial
    exact hy
  let χ := IsOpenImmersion.lift ((affineOpenCover K n).openCover.f j) p hrange
  have hχ : χ ≫ (affineOpenCover K n).openCover.f j = p :=
    IsOpenImmersion.lift_fac _ _ _
  have hbase : CommRingCat.ofHom (algebraMap K
      (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j))) ≫
      Spec.preimage χ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    calc
      _ = χ ≫ ((affineOpenCover K n).openCover.f j ≫ projectiveSpaceToSpec K n) :=
        congrArg (fun g => χ ≫ g) (affineOpenCover_comp_toSpec K n j).symm
      _ = (χ ≫ (affineOpenCover K n).openCover.f j) ≫ projectiveSpaceToSpec K n :=
        (Category.assoc _ _ _).symm
      _ = p ≫ projectiveSpaceToSpec K n := congrArg (fun g => g ≫ _) hχ
      _ = _ := hp
  let φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j) →ₐ[K] K :=
    { (Spec.preimage χ).hom with
      commutes' r := by
        have h := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f r) hbase
        exact h }
  refine ⟨j, φ, ?_⟩
  change Spec.map (Spec.preimage χ) ≫ (affineOpenCover K n).openCover.f j = p
  rw [Spec.map_preimage]
  exact hχ

/-- A chosen affine coordinate chart containing an actual rational point. -/
def pointChartIndex (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) : Fin (n + 1) :=
  Classical.choose (exists_chartPoint n p hp)

/-- The chosen chart map of an actual rational point, as an algebra map over its field. -/
def pointChartMap (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X (pointChartIndex n p hp)) →ₐ[K] K :=
  Classical.choose (Classical.choose_spec (exists_chartPoint n p hp))

@[simp]
theorem chartPoint_pointChartMap (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    chartPoint n (pointChartIndex n p hp) (pointChartMap n p hp) = p :=
  Classical.choose_spec (Classical.choose_spec (exists_chartPoint n p hp))

/-- Normalized, nonzero homogeneous coordinates for an actual rational point over its field. -/
def pointCoordinates (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) : Fin (n + 1) → K :=
  chartCoordinates n (pointChartIndex n p hp) (pointChartMap n p hp)

@[simp]
theorem pointCoordinates_index (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    pointCoordinates n p hp (pointChartIndex n p hp) = 1 :=
  chartCoordinates_self n _ _

theorem pointCoordinates_ne_zero (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    pointCoordinates n p hp ≠ 0 :=
  chartCoordinates_ne_zero n _ _

/-- Linear vanishing agrees with homogeneous-prime incidence at every actual rational point. -/
theorem pointCoordinates_linearForm_mem_iff
    (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K) :
    (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
      (p (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
        ℓ (pointCoordinates n p hp) = 0 := by
  have h := chartPoint_linearForm_mem_iff n (pointChartIndex n p hp) (pointChartMap n p hp) ℓ
  simpa only [chartPoint_pointChartMap, pointCoordinates] using h

/-- Evaluation detects incidence for every actual homogeneous degree-one polynomial. -/
theorem pointCoordinates_mem_iff
    (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (f : projectiveSpaceGrading K n 1) :
    (f : ProjectiveCoordinateRing K n) ∈ (p (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      MvPolynomial.eval (pointCoordinates n p hp) f = 0 := by
  have h := pointCoordinates_linearForm_mem_iff n p hp
    ((linearFormPolynomialEquiv K n).symm f)
  simpa only [LinearEquiv.apply_symm_apply, eval_eq_inverse_linearFormPolynomialEquiv] using h

end Langlands.AlgebraicGeometry.ProjectiveSpace
