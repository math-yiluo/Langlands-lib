import Langlands.Geometry.Analytic.AdmissibleEpimorphism
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AnalytificationCenter

/-! # Matched radius charts for a surjective affine algebra map -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set PresentedAffinoidAlgebra AnalyticAffineSpace
open LocalizedFunctorialityComparison.OriginalStrongMaps

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

set_option backward.isDefEq.respectTransparency false in
/-- A point lies on a radius chart exactly when its polynomial generators
satisfy the radius bounds. -/
theorem mem_range_chart_iff_generator_bounds (m : ℕ) (x : Space K P) :
    x ∈ Set.range (chart K P m) ↔
      ∀ i, pointSeminorm K P x (P.map (MvPolynomial.X i)) ≤ radius K m := by
  constructor
  · rintro ⟨s, rfl⟩ i
    rw [pointSeminorm_chart, chartSeminorm_apply, ← coordinate_eq_algebraMap P m i]
    exact (s.le_norm _).trans (norm_coordinate_le K (algebra K P m) i)
  · intro h
    let s := SeminormComparison.chartPoint (pointSeminorm_extendsNorm K P x) h
    refine ⟨s, SeminormComparison.pointSeminorm_injective K P ?_⟩
    rw [pointSeminorm_chart, SeminormComparison.chartSeminorm_chartPoint]

variable {B : Type w} [CommRing B] [Algebra K B] (f : A →ₐ[K] B)
  (hf : Function.Surjective f)

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Present the quotient algebra by the images of the original generators. -/
def quotientPolynomialPresentation : FinitePolynomialPresentation K B :=
  ⟨P.arity, f.comp P.map, hf.comp P.surjective⟩

local notation "Q" => quotientPolynomialPresentation K P f hf

/-- The bounded map between charts with the same radius uses the same
Tate series on the two sides. -/
def quotientRadiusMap (m : ℕ) : BoundedAlgHom K (algebra K P m) (algebra K Q m) :=
  PresentedAffinoidAlgebra.descendRelations K P.arity (polyradius K P.arity m)
    (PolynomialLocus.relations P (polyradius K P.arity m)) (algebra K Q m)
    (presentationMap K (algebra K Q m)) (by
      rintro _ ⟨p, hp, rfl⟩
      apply PolynomialLocus.polynomialMap_relation Q
      have hp' : P.map p = 0 := RingHom.mem_ker.mp hp
      change f (P.map p) = 0
      rw [hp', map_zero])

omit [CompleteSpace K] in
set_option backward.isDefEq.respectTransparency false in
theorem quotientRadiusMap_algebraMap (m : ℕ) (a : A) :
    quotientRadiusMap K P f hf m (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) =
      PolynomialLocus.algebraMap Q (polyradius K P.arity m) (f a) := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map P _ p]
  exact (PolynomialLocus.algebraMap_map Q (polyradius K P.arity m) p).symm

omit [CompleteSpace K] in
/-- Norm-controlled lifts through the common Tate algebra make the matched
chart map an admissible epimorphism. -/
theorem quotientRadiusMap_isAdmissibleEpi (m : ℕ) :
    (quotientRadiusMap K P f hf m).IsAdmissibleEpi := by
  obtain ⟨C, hC, hLift⟩ :=
    (BoundedAlgHom.isAdmissibleEpi_iff_normControlledLifts
      (presentationMap K (algebra K Q m))).mp
      (presentationMap_isAdmissibleEpi K (algebra K Q m))
  refine (BoundedAlgHom.isAdmissibleEpi_iff_normControlledLifts _).mpr ⟨C, hC, fun b => ?_⟩
  obtain ⟨s, hs, hn⟩ := hLift b
  exact ⟨presentationMap K (algebra K P m) s, hs,
    (norm_presentationMap_le K (algebra K P m) s).trans hn⟩

/-- For the presentation by quotient generators, each matched chart is
the full inverse image of the target chart on underlying spaces. -/
theorem preimage_range_chart_quotient (m : ℕ) :
    baseMap K P Q f ⁻¹' Set.range (chart K P m) = Set.range (chart K Q m) := by
  ext x
  change baseMap K P Q f x ∈ Set.range (chart K P m) ↔ x ∈ Set.range (chart K Q m)
  rw [mem_range_chart_iff_generator_bounds, mem_range_chart_iff_generator_bounds]
  simp only [pointSeminorm_baseMap]
  rfl

end Langlands.Analytic.AffineAnalytification
