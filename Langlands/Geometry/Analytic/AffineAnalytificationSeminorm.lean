import Langlands.Geometry.Analytic.AffineAnalytificationGluing
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # The multiplicative seminorm of a point of the affine analytification -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- A multiplicative seminorm on the `K`-algebra `A` extends the norm of `K` if it
takes the value `‖c‖` at the image of every scalar `c`. -/
def ExtendsNorm (ν : MulRingSeminorm A) : Prop :=
  ∀ c : K, ν (algebraMap K A c) = ‖c‖

variable (P : FinitePolynomialPresentation K A)

/-- The multiplicative seminorm `a ↦ s(a)` on `A` of a point `s` of the `m`-th bounded
chart, obtained by evaluating `s` on the image of `a` in the chart algebra. -/
def chartSeminorm (m : ℕ) (s : BanachSpectrum (algebra K P m)) : MulRingSeminorm A where
  toFun a := s (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)
  map_zero' := by
    change s.toMulRingSeminorm (PolynomialLocus.algebraMap P _ 0) = 0
    rw [map_zero, map_zero]
  map_one' := by
    change s.toMulRingSeminorm (PolynomialLocus.algebraMap P _ 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    change s.toMulRingSeminorm (PolynomialLocus.algebraMap P _ (a * b)) = _
    rw [map_mul, map_mul]
  add_le' a b := by
    change s.toMulRingSeminorm (PolynomialLocus.algebraMap P _ (a + b)) ≤ _
    rw [map_add]
    exact map_add_le_add s.toMulRingSeminorm _ _
  neg' a := by
    change s.toMulRingSeminorm (PolynomialLocus.algebraMap P _ (-a)) = _
    rw [map_neg, map_neg_eq_map]

@[simp]
theorem chartSeminorm_apply (m : ℕ) (s : BanachSpectrum (algebra K P m)) (a : A) :
    chartSeminorm K P m s a = s (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) :=
  rfl

variable [CompleteSpace K]

/-- Pulling a chart point back to a larger chart does not change its seminorm on `A`. -/
theorem chartSeminorm_pull {m k : ℕ} (h : m ≤ k) (s : BanachSpectrum (algebra K P m)) :
    chartSeminorm K P k ((chartSystem K P).pull h s) = chartSeminorm K P m s := by
  ext a
  change s (restriction K P h (PolynomialLocus.algebraMap P (polyradius K P.arity k) a)) =
    s (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)
  change s (PolynomialLocus.restriction P _ _ _
    (PolynomialLocus.algebraMap P (polyradius K P.arity k) a)) = _
  rw [PolynomialLocus.restriction_algebraMap]

theorem chartSeminorm_glued {m k : ℕ} {s : BanachSpectrum (algebra K P m)}
    {t : BanachSpectrum (algebra K P k)} (h : (chartSystem K P).Glued m s k t) :
    chartSeminorm K P m s = chartSeminorm K P k t := by
  obtain ⟨l, hlm, hlk, v, rfl, rfl⟩ := h
  exact (chartSeminorm_pull K P hlm v).trans (chartSeminorm_pull K P hlk v).symm

/-- The multiplicative seminorm on `A` of a point of the glued analytic space. -/
def pointSeminorm : Space K P → MulRingSeminorm A :=
  Quotient.lift (fun p => chartSeminorm K P p.1 p.2)
    (fun _ _ h => chartSeminorm_glued K P h)

@[simp]
theorem pointSeminorm_chart (m : ℕ) (s : BanachSpectrum (algebra K P m)) :
    pointSeminorm K P (chart K P m s) = chartSeminorm K P m s :=
  rfl

/-- Each evaluation `x ↦ |a|_x` is continuous on the glued space. -/
theorem continuous_pointSeminorm_apply (a : A) :
    Continuous (fun x : Space K P => pointSeminorm K P x a) := by
  have e : (fun x : Space K P => pointSeminorm K P x a) =
      Quotient.lift (fun p : (m : ℕ) × BanachSpectrum (algebra K P m) =>
        chartSeminorm K P p.1 p.2 a)
        (fun _ _ h => congrArg (fun ν : MulRingSeminorm A => ν a)
          (chartSeminorm_glued K P h)) := by
    funext x
    induction x using Quotient.inductionOn
    rfl
  rw [e]
  exact Continuous.quotient_lift (continuous_sigma fun m =>
    (BanachSpectrum.evaluation
      (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)).continuous) _

/-- The seminorm of every point extends the norm of `K`. -/
theorem pointSeminorm_extendsNorm (x : Space K P) : ExtendsNorm K (pointSeminorm K P x) := by
  obtain ⟨m, s, rfl⟩ := exists_chart K P x
  intro c
  rw [pointSeminorm_chart, chartSeminorm_apply, AlgHom.commutes]
  exact BanachSpectrum.algebraMap_apply s c

end Langlands.Analytic.AffineAnalytification
