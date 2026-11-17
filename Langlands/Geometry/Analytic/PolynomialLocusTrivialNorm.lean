import Langlands.Geometry.Analytic.PolynomialLocusCharts
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelationsUniversalProperty
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximation

/-! # Unit-radius polynomial-locus charts over a trivially normed field

When every nonzero scalar has norm one, a unit-radius weighted Tate series has only
finitely many nonzero coefficients, so it is a polynomial.  Consequently the
unit-radius chart of a finite polynomial presentation `P` of a `K`-algebra `A` is
the image of `A`, every element has norm at most one, and bounded maps out of the
chart are exactly the algebra maps out of `A` with values of norm at most one.
-/

noncomputable section

universe u v w

namespace Langlands.Analytic.PolynomialLocus

open GeneralizedTateAlgebra PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

section Tate

variable {σ : Type*}

/-- Over a trivially normed field every unit-radius weighted Tate series has norm at
most one. -/
theorem tate_norm_le_one (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K) : ‖f‖ ≤ 1 := by
  apply (norm_le_iff _ K f zero_le_one).mpr
  intro d
  rw [PositivePolyradius.unit_weight, mul_one]
  rcases eq_or_ne (MvPowerSeries.coeff d (series _ K f)) 0 with h | h
  · rw [h, norm_zero]
    exact zero_le_one
  · exact (hK _ h).le

/-- Over a trivially normed field a unit-radius weighted Tate series of norm less
than one vanishes. -/
theorem tate_eq_zero_of_norm_lt_one (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K) (hf : ‖f‖ < 1) :
    f = 0 := by
  have hcoeff : ∀ d, MvPowerSeries.coeff d (series _ K f) = 0 := by
    intro d
    by_contra h
    have hle := weighted_norm_coeff_le _ K f d
    rw [PositivePolyradius.unit_weight, mul_one, hK _ h] at hle
    exact absurd (hle.trans_lt hf) (lt_irrefl 1)
  apply Subtype.ext
  ext d
  exact hcoeff d

/-- Over a trivially normed field every unit-radius weighted Tate series is a
polynomial. -/
theorem tate_polynomialMap_surjective (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1) :
    Function.Surjective
      (GeneralizedTateAlgebra.polynomialMap (PositivePolyradius.unit σ) K) := by
  intro f
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ :=
    Metric.mem_closure_iff.mp (denseRange_polynomialMap (PositivePolyradius.unit σ) K f)
      1 one_pos
  refine ⟨p, ?_⟩
  have h := tate_eq_zero_of_norm_lt_one hK
    (f - GeneralizedTateAlgebra.polynomialMap (PositivePolyradius.unit σ) K p)
    (by rwa [← dist_eq_norm])
  exact (sub_eq_zero.mp h).symm

end Tate

variable {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- Over a trivially normed field the algebra map onto the unit-radius chart is
surjective. -/
theorem algebraMap_surjective (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1) :
    Function.Surjective (algebraMap P (PositivePolyradius.unit (Fin P.arity))) := by
  intro s
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (chart P (PositivePolyradius.unit _)) s
  obtain ⟨p, rfl⟩ := tate_polynomialMap_surjective hK f
  exact ⟨P.map p, algebraMap_map P _ p⟩

/-- Over a trivially normed field every element of the unit-radius chart has norm at
most one. -/
theorem norm_le_one (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (s : chart P (PositivePolyradius.unit (Fin P.arity))) : ‖s‖ ≤ 1 := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (chart P (PositivePolyradius.unit _)) s
  exact (norm_presentationMap_le K _ f).trans (tate_norm_le_one hK f)

/-- Over a trivially normed field an element of the unit-radius chart of norm less
than one vanishes. -/
theorem eq_zero_of_norm_lt_one (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    (s : chart P (PositivePolyradius.unit (Fin P.arity))) (hs : ‖s‖ < 1) : s = 0 := by
  obtain ⟨f, hfs, hf⟩ := exists_representative_norm_lt K
    (chart P (PositivePolyradius.unit _)) s (sub_pos.mpr hs)
  rw [add_sub_cancel] at hf
  have h0 : f = 0 := tate_eq_zero_of_norm_lt_one hK f hf
  rw [← hfs, h0, map_zero]

section Lift

variable {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

omit [IsUltrametricDist K] in
/-- An algebra map out of `A` is polynomial evaluation at the images of the
presentation variables. -/
theorem comp_map_eq_aeval (g : A →ₐ[K] B) :
    g.comp P.map = MvPolynomial.aeval (fun i => g (P.map (MvPolynomial.X i))) :=
  MvPolynomial.aeval_unique (g.comp P.map)

omit [IsUltrametricDist K] in
/-- The images of the presentation variables under an algebra map with values of
norm at most one have unit-weight bounded monomials. -/
theorem hasBoundedMonomials_of_norm_le_one (g : A →ₐ[K] B) (hg : ∀ a, ‖g a‖ ≤ 1) :
    HasBoundedMonomials (PositivePolyradius.unit (Fin P.arity)) B
      (fun i => g (P.map (MvPolynomial.X i))) := by
  refine ⟨1, one_pos, fun d => ?_⟩
  rw [PositivePolyradius.unit_weight, mul_one]
  have h : StrictTateAlgebra.monomialValue (Fin P.arity) B
      (fun i => g (P.map (MvPolynomial.X i))) d = g (P.map (MvPolynomial.monomial d 1)) := by
    rw [← AlgHom.comp_apply, comp_map_eq_aeval, MvPolynomial.aeval_monomial, map_one,
      one_mul]
    rfl
  rw [h]
  exact hg _

variable [IsUltrametricDist B] [CompleteSpace B]

/-- Weighted evaluation of a polynomial is polynomial evaluation. -/
theorem evaluate_polynomialMap (b : Fin P.arity → B)
    (hb : HasBoundedMonomials (PositivePolyradius.unit (Fin P.arity)) B b)
    (p : MvPolynomial (Fin P.arity) K) :
    evaluate (PositivePolyradius.unit (Fin P.arity)) K B b
        (GeneralizedTateAlgebra.polynomialMap (PositivePolyradius.unit (Fin P.arity)) K p) =
      MvPolynomial.aeval b p := by
  have h : (evaluateHom (PositivePolyradius.unit (Fin P.arity)) K B b hb).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap (PositivePolyradius.unit (Fin P.arity)) K) =
        MvPolynomial.aeval b := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, GeneralizedTateAlgebra.polynomialMap, MvPolynomial.aeval_X]
    exact evaluate_X (PositivePolyradius.unit (Fin P.arity)) K B b i
  exact DFunLike.congr_fun h p

/-- The bounded map out of the unit-radius chart induced by an algebra map out of `A`
with values of norm at most one. -/
def lift (g : A →ₐ[K] B) (hg : ∀ a, ‖g a‖ ≤ 1) :
    BoundedAlgHom K (chart P (PositivePolyradius.unit (Fin P.arity))) B :=
  evaluateRelations K B P.arity (PositivePolyradius.unit (Fin P.arity))
    (relations P (PositivePolyradius.unit (Fin P.arity)))
    (fun i => g (P.map (MvPolynomial.X i)))
    (hasBoundedMonomials_of_norm_le_one P g hg)
    (by
      rintro _ ⟨p, hp, rfl⟩
      rw [evaluate_polynomialMap P _ (hasBoundedMonomials_of_norm_le_one P g hg),
        ← comp_map_eq_aeval, AlgHom.comp_apply]
      change g (P.map p) = 0
      rw [show P.map p = 0 from hp, map_zero])

@[simp]
theorem lift_algebraMap (g : A →ₐ[K] B) (hg : ∀ a, ‖g a‖ ≤ 1) (a : A) :
    lift P g hg (algebraMap P (PositivePolyradius.unit (Fin P.arity)) a) = g a := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [algebraMap_map]
  change evaluate (PositivePolyradius.unit (Fin P.arity)) K B _
    (GeneralizedTateAlgebra.polynomialMap (PositivePolyradius.unit (Fin P.arity)) K p) = _
  rw [evaluate_polynomialMap P _ (hasBoundedMonomials_of_norm_le_one P g hg),
    ← comp_map_eq_aeval, AlgHom.comp_apply]

end Lift

/-- Over a trivially normed field bounded maps out of the unit-radius chart are
determined by their values on the image of `A`. -/
theorem hom_ext (hK : ∀ c : K, c ≠ 0 → ‖c‖ = 1)
    {B : Type w} [NormedCommRing B] [Algebra K B]
    (φ ψ : BoundedAlgHom K (chart P (PositivePolyradius.unit (Fin P.arity))) B)
    (h : ∀ a, φ (algebraMap P (PositivePolyradius.unit (Fin P.arity)) a) =
      ψ (algebraMap P (PositivePolyradius.unit (Fin P.arity)) a)) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro s
  obtain ⟨a, rfl⟩ := algebraMap_surjective P hK s
  exact h a

end Langlands.Analytic.PolynomialLocus
