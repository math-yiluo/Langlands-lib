import Langlands.Geometry.Analytic.AffineAnalytificationAtlas
import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation
import Langlands.AlgebraicGeometry.PointTopology.Affine

/-! # Rational points of the polynomial-locus analytification -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-! ## Algebraic points and their polydisc radii -/

/-- The coordinates of an algebraic point in the presentation variables. -/
def pointCoordinates (φ : AlgPoint K A K) (i : Fin P.arity) : K :=
  φ (P.map (MvPolynomial.X i))

/-- The `m`-th closed polydisc of the construction contains the coordinates of `φ`. -/
def RadiusAdmits (φ : AlgPoint K A K) (m : ℕ) : Prop :=
  ∀ i, ‖pointCoordinates K P φ i‖ ≤ radius K m

variable {K P}

theorem RadiusAdmits.mono {φ : AlgPoint K A K} {m k : ℕ} (hm : RadiusAdmits K P φ m)
    (h : m ≤ k) : RadiusAdmits K P φ k :=
  fun i => (hm i).trans ((radius_le_radius_iff K).2 h)

variable (K P)

theorem exists_radiusAdmits (φ : AlgPoint K A K) : ∃ m, RadiusAdmits K P φ m := by
  obtain ⟨m, hm⟩ := exists_radius_gt K (∑ i, ‖pointCoordinates K P φ i‖)
  refine ⟨m, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (pointCoordinates K P φ j))
    (Finset.mem_univ i)).trans hm.le

open scoped Classical in
/-- The least radius index admitted by `φ`. -/
def minimalRadius (φ : AlgPoint K A K) : ℕ :=
  Nat.find (exists_radiusAdmits K P φ)

open scoped Classical in
theorem radiusAdmits_minimalRadius (φ : AlgPoint K A K) :
    RadiusAdmits K P φ (minimalRadius K P φ) :=
  Nat.find_spec (exists_radiusAdmits K P φ)

open scoped Classical in
theorem minimalRadius_le {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    minimalRadius K P φ ≤ m :=
  Nat.find_min' (exists_radiusAdmits K P φ) hm

/-- Admissible coordinates have weighted monomials bounded by one. -/
theorem hasBoundedMonomials {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    GeneralizedTateAlgebra.HasBoundedMonomials (polyradius K P.arity m) K
      (pointCoordinates K P φ) := by
  refine ⟨1, one_pos, fun d => ?_⟩
  rw [one_mul]
  unfold StrictTateAlgebra.monomialValue PositivePolyradius.weight
  rw [Finsupp.prod, Finsupp.prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hm i) _

/-! ## Evaluation characters of the bounded charts -/

variable [IsUltrametricDist K] [CompleteSpace K]

/-- Weighted Tate evaluation at the coordinates of `φ`. -/
def tateEvaluation {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    BoundedAlgHom K (GeneralizedTateAlgebra (polyradius K P.arity m) K) K :=
  GeneralizedTateAlgebra.evaluateHom (polyradius K P.arity m) K K (pointCoordinates K P φ)
    (hasBoundedMonomials K P hm)

theorem tateEvaluation_X {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m)
    (i : Fin P.arity) :
    tateEvaluation K P hm (GeneralizedTateAlgebra.X (polyradius K P.arity m) K i) =
      pointCoordinates K P φ i :=
  GeneralizedTateAlgebra.evaluate_X (polyradius K P.arity m) K K (pointCoordinates K P φ) i

/-- On polynomials, Tate evaluation is the algebraic point itself. -/
theorem tateEvaluation_polynomialMap {φ : AlgPoint K A K} {m : ℕ}
    (hm : RadiusAdmits K P φ m) (p : MvPolynomial (Fin P.arity) K) :
    tateEvaluation K P hm (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p) =
      φ (P.map p) := by
  have h : (tateEvaluation K P hm).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K) =
        (AlgPoint.toAlgHom φ).comp P.map := by
    apply MvPolynomial.algHom_ext
    intro i
    change tateEvaluation K P hm (MvPolynomial.aeval _ (MvPolynomial.X i)) =
      pointCoordinates K P φ i
    rw [MvPolynomial.aeval_X]
    exact tateEvaluation_X K P hm i
  exact AlgHom.congr_fun h p

/-- The bounded `K`-valued character of the `m`-th polynomial-locus chart
defined by `φ`. -/
def character {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    BoundedAlgHom K (algebra K P m) K :=
  PresentedAffinoidAlgebra.descendRelations K P.arity (polyradius K P.arity m)
    (PolynomialLocus.relations P (polyradius K P.arity m)) K (tateEvaluation K P hm)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have h0 : P.map p = 0 := RingHom.mem_ker.1 hp
      rw [tateEvaluation_polynomialMap, h0]
      exact map_zero (AlgPoint.toAlgHom φ))

theorem character_presentationMap {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m)
    (f : GeneralizedTateAlgebra (polyradius K P.arity m) K) :
    character K P hm (presentationMap K (algebra K P m) f) = tateEvaluation K P hm f :=
  rfl

theorem character_coordinate {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m)
    (i : Fin P.arity) :
    character K P hm (coordinate K (algebra K P m) i) = pointCoordinates K P φ i :=
  tateEvaluation_X K P hm i

theorem character_algebraMap {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m)
    (a : A) :
    character K P hm (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) = φ a := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  exact tateEvaluation_polynomialMap K P hm p

/-- The characters are compatible with the actual radius restrictions. -/
theorem character_comp_restriction {φ : AlgPoint K A K} {m k : ℕ}
    (hm : RadiusAdmits K P φ m) (h : m ≤ k) :
    (character K P hm).comp (restriction K P h) = character K P (hm.mono h) := by
  have e : ((character K P hm).comp (restriction K P h)).comp
      (presentationMap K (algebra K P k)) = tateEvaluation K P (hm.mono h) := by
    apply GeneralizedTateAlgebra.hom_ext
    intro (i : Fin P.arity)
    change character K P hm (restriction K P h (coordinate K (algebra K P k) i)) =
      tateEvaluation K P (hm.mono h) (GeneralizedTateAlgebra.X _ K i)
    rw [tateEvaluation_X]
    change character K P hm (PolynomialLocus.restriction P _ _ _
      (coordinate K (PolynomialLocus.chart P (polyradius K P.arity k)) i)) = _
    rw [PolynomialLocus.restriction_coordinate]
    exact character_coordinate K P hm i
  apply PresentedAffinoidAlgebra.hom_ext_presentation K K
  intro f
  exact congrArg (fun g : BoundedAlgHom K _ K => g f) e

/-! ## The analytic point of an algebraic point -/

/-- The spectrum point `a ↦ ‖χ(a)‖` of the evaluation character. -/
def spectrumPoint {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    BanachSpectrum (algebra K P m) :=
  BanachSpectrum.comap (character K P hm).toBoundedRingHom (BanachSpectrum.fieldPoint K)

theorem spectrumPoint_apply {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m)
    (a : algebra K P m) :
    spectrumPoint K P hm a = ‖character K P hm a‖ :=
  rfl

theorem pull_spectrumPoint {φ : AlgPoint K A K} {m k : ℕ} (hm : RadiusAdmits K P φ m)
    (h : m ≤ k) :
    (chartSystem K P).pull h (spectrumPoint K P hm) = spectrumPoint K P (hm.mono h) := by
  ext a
  change ‖character K P hm (restriction K P h a)‖ = ‖character K P (hm.mono h) a‖
  rw [← character_comp_restriction K P hm h]
  rfl

/-- The point of the constructed analytic space defined by an algebraic point. -/
def analyticPoint (φ : AlgPoint K A K) : Space K P :=
  chart K P (minimalRadius K P φ) (spectrumPoint K P (radiusAdmits_minimalRadius K P φ))

/-- Every admissible chart computes the same analytic point. -/
theorem chart_spectrumPoint {φ : AlgPoint K A K} {m : ℕ} (hm : RadiusAdmits K P φ m) :
    chart K P m (spectrumPoint K P hm) = analyticPoint K P φ := by
  rw [analyticPoint, ← chart_pull K P (minimalRadius_le K P hm), pull_spectrumPoint]

theorem coordinateNorm_analyticPoint (φ : AlgPoint K A K) (i : Fin P.arity) :
    coordinateNorm K P i (analyticPoint K P φ) = ‖pointCoordinates K P φ i‖ := by
  rw [analyticPoint, coordinateNorm_chart, spectrumPoint_apply, character_coordinate]

theorem analyticPoint_mem_range_chart_iff (φ : AlgPoint K A K) (m : ℕ) :
    analyticPoint K P φ ∈ range (chart K P m) ↔ RadiusAdmits K P φ m := by
  rw [mem_range_chart_iff]
  simp only [coordinateNorm_analyticPoint, RadiusAdmits]

/-! ## Comparison with field-valued points of the constructed atlas -/

open AffinoidAtlasPresentation

/-- The `K`-valued point of the constructed affinoid atlas defined by an algebraic
point: on each chart containing it, its evaluation character. -/
def toFieldPoint (φ : AlgPoint K A K) : FieldPoint K (presentation K P) where
  point := analyticPoint K P φ
  eval i h := (character K P ((analyticPoint_mem_range_chart_iff K P φ i.val).1 h)).toAlgHom
  isChartPoint i h :=
    ⟨spectrumPoint K P ((analyticPoint_mem_range_chart_iff K P φ i.val).1 h),
      chart_spectrumPoint K P _, fun _ => rfl⟩
  eval_restriction i j hij hi :=
    congrArg BoundedAlgHom.toAlgHom (character_comp_restriction K P
      ((analyticPoint_mem_range_chart_iff K P φ i.val).1 hi)
      ((selected_range_subset_iff K P i j).1 hij))

@[simp]
theorem toFieldPoint_point (φ : AlgPoint K A K) :
    (toFieldPoint K P φ).point = analyticPoint K P φ :=
  rfl

/-- The coordinate-algebra map into the algebra of a chart of the constructed atlas. -/
def chartAlgebraMap (i : (presentation K P).atlas.Index) :
    A →ₐ[K] (presentation K P).atlas.algebra i :=
  PolynomialLocus.algebraMap P (polyradius K P.arity i.val)

/-- A chart of the constructed atlas containing the point of `p`. -/
def chosenChart (p : FieldPoint K (presentation K P)) : (presentation K P).atlas.Index :=
  (IndexedAffinoidAtlas.exists_mem_range_chart (presentation K P).atlas p.point).choose

theorem mem_range_chosenChart (p : FieldPoint K (presentation K P)) :
    p.point ∈ range ((presentation K P).atlas.chart (chosenChart K P p)) :=
  (IndexedAffinoidAtlas.exists_mem_range_chart (presentation K P).atlas p.point).choose_spec

/-- The algebraic point underlying a `K`-valued point of the constructed atlas:
its evaluation at a chart containing the point, composed with the
coordinate-algebra map. -/
def toAlgPoint (p : FieldPoint K (presentation K P)) : AlgPoint K A K :=
  AlgPoint.ofAlgHom ((p.eval (chosenChart K P p) (mem_range_chosenChart K P p)).comp
    (chartAlgebraMap K P (chosenChart K P p)))

/-- The algebraic point may be computed at any chart containing the point. -/
theorem toAlgPoint_apply_eq (p : FieldPoint K (presentation K P))
    (i : (presentation K P).atlas.Index) (hi : p.point ∈ range ((presentation K P).atlas.chart i))
    (a : A) :
    toAlgPoint K P p a = p.eval i hi (chartAlgebraMap K P i a) := by
  have key : ∀ j (hj : p.point ∈ range ((presentation K P).atlas.chart j))
      (k : (presentation K P).atlas.Index)
      (hkj : range ((presentation K P).atlas.chart k) ⊆ range ((presentation K P).atlas.chart j))
      (hk : p.point ∈ range ((presentation K P).atlas.chart k)),
      p.eval j hj (chartAlgebraMap K P j a) = p.eval k hk (chartAlgebraMap K P k a) := by
    intro j hj k hkj hk
    rw [← p.eval_restriction k j hkj hk]
    change p.eval k hk (restriction K P ((selected_range_subset_iff K P k j).1 hkj)
      (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a)) = _
    change p.eval k hk (PolynomialLocus.restriction P _ _ _
      (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a)) = _
    rw [PolynomialLocus.restriction_algebraMap]
    rfl
  set j := chosenChart K P p
  have hj := mem_range_chosenChart K P p
  set k := representative K P (min i.val j.val)
  have hk_range : range ((presentation K P).atlas.chart k) =
      range (chart K P (min i.val j.val)) :=
    range_representative K P (min i.val j.val)
  have hki : range ((presentation K P).atlas.chart k) ⊆ range ((presentation K P).atlas.chart i) := by
    rw [hk_range]
    exact range_chart_mono K P (min_le_left _ _)
  have hkj : range ((presentation K P).atlas.chart k) ⊆ range ((presentation K P).atlas.chart j) := by
    rw [hk_range]
    exact range_chart_mono K P (min_le_right _ _)
  have hk : p.point ∈ range ((presentation K P).atlas.chart k) := by
    rw [hk_range]
    rcases le_total i.val j.val with h | h
    · rw [min_eq_left h]
      exact hi
    · rw [min_eq_right h]
      exact hj
  change p.eval j hj (chartAlgebraMap K P j a) = _
  rw [key j hj k hkj hk, key i hi k hki hk]

/-- Field-valued points recover their algebraic points. -/
theorem toAlgPoint_toFieldPoint (φ : AlgPoint K A K) :
    toAlgPoint K P (toFieldPoint K P φ) = φ := by
  ext a
  exact character_algebraMap K P
    ((analyticPoint_mem_range_chart_iff K P φ (chosenChart K P (toFieldPoint K P φ)).val).1
      (mem_range_chosenChart K P (toFieldPoint K P φ))) a

end Langlands.Analytic.AffineAnalytification
