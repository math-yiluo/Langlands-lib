import Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates

/-! # Global coordinates on a unit projective chart -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (n : ℕ) {X : Scheme.{u}}

local notation "𝒜" => projectiveSpaceGrading R n

local instance (j : Fin (n + 1)) : Algebra R
    (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway R n j

/-- Evaluate a homogeneous affine chart when the chart denominator evaluates to a unit. -/
def unitChartRingMap {B : Type u} [CommRing B]
    (f : ProjectiveCoordinateRing R n →+* B) (t : ProjectiveCoordinateRing R n)
    (ht : IsUnit (f t)) : Away 𝒜 t →+* B :=
  (Localization.awayLift f t ht).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- Unit-chart evaluation recovers the localized chart map after the target localization. -/
theorem chartRingMap_eq_unitChartRingMap {B : Type u} [CommRing B]
    (f : ProjectiveCoordinateRing R n →+* B) (t : ProjectiveCoordinateRing R n)
    (ht : IsUnit (f t)) :
    chartRingMap n f t = (algebraMap B (Localization.Away (f t))).comp
      (unitChartRingMap n f t ht) := by
  have h : IsLocalization.map (M := .powers t) (T := .powers (f t))
      (Localization.Away (f t)) f (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]) =
      (algebraMap B (Localization.Away (f t))).comp (Localization.awayLift f t ht) := by
    apply IsLocalization.ringHom_ext (M := .powers t)
    simp only [IsLocalization.map_comp, RingHom.comp_assoc, Localization.awayLift,
      IsLocalization.Away.lift_comp]
  unfold chartRingMap unitChartRingMap
  rw [h, RingHom.comp_assoc]

/-- A unit of global sections has the whole scheme as its basic open. -/
theorem isIso_basicOpen_ι_of_isUnit (f : Γ(X, ⊤)) (hf : IsUnit f) :
    IsIso (X.basicOpen f).ι := by
  rw [X.basicOpen_of_isUnit hf]
  change IsIso X.topIso.hom
  infer_instance

/-- With a unit chart coordinate, the actual projective map is the corresponding
map into the affine chart, expressed through global sections. -/
theorem fromOfGlobalSections_eq_unitChart
    (f : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {d : ℕ} (hd : 0 < d) (t : ProjectiveCoordinateRing R n) (ht : t ∈ 𝒜 d)
    (hu : IsUnit (f t)) :
    Proj.fromOfGlobalSections 𝒜 f hf = X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (unitChartRingMap n f t hu)) ≫ Proj.awayι 𝒜 t ht hd := by
  let : IsIso (X.basicOpen (f t)).ι := isIso_basicOpen_ι_of_isUnit (f t) hu
  apply (cancel_epi (X.basicOpen (f t)).ι).mp
  rw [basicOpen_ι_fromOfGlobalSections n f hf hd t ht]
  simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι]
  change _ ≫ _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (chartRingMap n f t)) ≫ _ = _
  rw [chartRingMap_eq_unitChartRingMap n f t hu, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap_assoc,
    morphismRestrict_ι_assoc, Scheme.isoOfEq_inv, Scheme.homOfLE_ι_assoc]

/-- The global-section adjunction detects equality of maps into affine schemes. -/
theorem toSpecΓ_specMap_eq_iff {B : Type u} [CommRing B]
    (f g : B →+* Γ(X, ⊤)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g) ↔ f = g := by
  constructor
  · intro h
    have h' := (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of B))).injective
      (show (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of B)))
          (CommRingCat.ofHom f).op =
        (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of B)))
          (CommRingCat.ofHom g).op from by
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) =
          X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g)
        exact h)
    exact congrArg (fun z => z.unop.hom) h'
  · rintro rfl
    rfl

/-- Two global-coordinate projective maps in a common unit chart are equal
exactly when their actual affine chart ring maps are equal. -/
theorem fromOfGlobalSections_eq_iff_unitChart
    (f g : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    {d : ℕ} (hd : 0 < d) (t : ProjectiveCoordinateRing R n) (ht : t ∈ 𝒜 d)
    (hfu : IsUnit (f t)) (hgu : IsUnit (g t)) :
    Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 g hg ↔
      unitChartRingMap n f t hfu = unitChartRingMap n g t hgu := by
  rw [fromOfGlobalSections_eq_unitChart n f hf hd t ht hfu,
    fromOfGlobalSections_eq_unitChart n g hg hd t ht hgu,
    ← Category.assoc, ← Category.assoc, cancel_mono,
    toSpecΓ_specMap_eq_iff]

/-- Evaluated degree-one chart ratios satisfy the exact coordinate identity. -/
theorem unitChartRingMap_ratio_mul {B : Type u} [CommRing B]
    (f : ProjectiveCoordinateRing R n →+* B) (j i : Fin (n + 1))
    (hj : IsUnit (f (MvPolynomial.X j))) :
    unitChartRingMap n f (MvPolynomial.X j) hj
        (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i) * f (MvPolynomial.X j) =
      f (MvPolynomial.X i) := by
  obtain ⟨u, hu⟩ := hj
  have hinv : f (MvPolynomial.X j) * (↑u⁻¹ : B) = 1 := by rw [← hu]; simp
  change Localization.awayLift f (MvPolynomial.X j) ⟨u, hu⟩
    (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i).val * f (MvPolynomial.X j) = _
  rw [_root_.AlgebraicGeometry.ProjSpace.ratio, Away.val_mk]
  rw [Localization.awayLift_mk f (MvPolynomial.X j) (MvPolynomial.X i)
    (↑u⁻¹ : B) hinv 1]
  simp only [pow_one, mul_assoc, ← hu, Units.inv_mul, mul_one]

/-- Evaluation on coefficient constants is unchanged on the homogeneous chart. -/
theorem unitChartRingMap_algebraMap {B : Type u} [CommRing B] [Algebra R B]
    (f : ProjectiveCoordinateRing R n →+* B) (j : Fin (n + 1))
    (hj : IsUnit (f (MvPolynomial.X j)))
    (hconst : ∀ r : R, f (MvPolynomial.C r) = algebraMap R B r) (r : R) :
    unitChartRingMap n f (MvPolynomial.X j) hj
      (algebraMap R (Away 𝒜 (MvPolynomial.X j)) r) = algebraMap R B r := by
  change Localization.awayLift f (MvPolynomial.X j) hj
    (algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j)) r).val = _
  rw [_root_.AlgebraicGeometry.ProjSpace.val_algebraMap, IsLocalization.Away.lift_eq]
  exact hconst r

/-- Common coefficient maps and equality on coordinate ratios determine the
whole homogeneous affine-chart map. -/
theorem unitChartRingMap_ext {B : Type u} [CommRing B] [Algebra R B]
    (f g : ProjectiveCoordinateRing R n →+* B) (j : Fin (n + 1))
    (hf : IsUnit (f (MvPolynomial.X j))) (hg : IsUnit (g (MvPolynomial.X j)))
    (hfc : ∀ r : R, f (MvPolynomial.C r) = algebraMap R B r)
    (hgc : ∀ r : R, g (MvPolynomial.C r) = algebraMap R B r)
    (h : ∀ i : Fin (n + 1),
      unitChartRingMap n f (MvPolynomial.X j) hf (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i) =
      unitChartRingMap n g (MvPolynomial.X j) hg (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i)) :
    unitChartRingMap n f (MvPolynomial.X j) hf = unitChartRingMap n g (MvPolynomial.X j) hg := by
  apply RingHom.ext
  intro z
  have hz : z ∈ Algebra.adjoin R (Set.range (_root_.AlgebraicGeometry.ProjSpace.ratio R n j)) := by
    rw [_root_.AlgebraicGeometry.ProjSpace.adjoin_range_ratio]
    trivial
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact h i
  | algebraMap r =>
    rw [unitChartRingMap_algebraMap n f j hf hfc, unitChartRingMap_algebraMap n g j hg hgc]
  | add z w _ _ hz hw => simp only [map_add, hz, hw]
  | mul z w _ _ hz hw => simp only [map_mul, hz, hw]

end Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates
