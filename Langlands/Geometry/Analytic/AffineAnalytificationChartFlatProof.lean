import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatCompletionProof
import Langlands.Geometry.Analytic.TatePolynomialFlatness
import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChange
import Langlands.Geometry.Analytic.PolynomialLocusCharts
import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Langlands.Geometry.Analytic.TateNoetherian
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Flat.Stability

/-! # Proof: the chart algebras of the affine analytification are flat -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace ChartFlatness

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Flatness passes to the induced map of quotients `R ⧸ I → S ⧸ I S`, which is the
base change of `f` along `R → R ⧸ I`. -/
theorem flat_quotientMap (f : R →+* S) (hf : f.Flat) (I : Ideal R) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by
  let _ := f.toAlgebra
  have : Module.Flat R S := hf
  have : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact RingHom.flat_algebraMap_iff.mpr this

end Quotient

section Rescale

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

open GeneralizedTateAlgebra AnalyticAffineSpace

/-- The scalar `ϖ⁻ᵐ`, whose norm is the radius of the `m`-th chart. -/
def chartScalar (m : ℕ) : K := (AnalyticAffineSpace.scale K)⁻¹ ^ m

omit [IsUltrametricDist K] in
theorem chartScalar_ne_zero (m : ℕ) : chartScalar K m ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (norm_pos_iff.mp (norm_scale_pos K)))

omit [IsUltrametricDist K] in
theorem norm_chartScalar (n m : ℕ) (i : Fin n) :
    ‖chartScalar K m‖ = AnalyticAffineSpace.polyradius K n m i := by
  change ‖(AnalyticAffineSpace.scale K)⁻¹ ^ m‖ = ‖AnalyticAffineSpace.scale K‖⁻¹ ^ m
  rw [norm_pow, norm_inv]

variable (n m : ℕ)

/-- The rescaling `∑ a_d T^d ↦ ∑ ϖ^{-m|d|} a_d T^d` from the weighted Tate algebra of
polyradius `(‖ϖ‖⁻ᵐ, …, ‖ϖ‖⁻ᵐ)` to the strict Tate algebra. -/
def chartRescale :
    GeneralizedTateAlgebra (AnalyticAffineSpace.polyradius K n m) K →+*
      StrictTateAlgebra (Fin n) K :=
  baseChange (AnalyticAffineSpace.polyradius K n m) (RingHom.id K)
    (c := fun _ => chartScalar K m) (norm_chartScalar K n m) (fun _ => rfl)

theorem coeff_chartRescale
    (f : GeneralizedTateAlgebra (AnalyticAffineSpace.polyradius K n m) K) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d (StrictTateAlgebra.series (Fin n) K (chartRescale K n m f)) =
      GeneralizedTateAlgebra.scale (fun _ : Fin n => chartScalar K m) d *
        MvPowerSeries.coeff d (series (AnalyticAffineSpace.polyradius K n m) K f) :=
  coeff_baseChange _ _ _ _ f d

theorem norm_chartRescale
    (f : GeneralizedTateAlgebra (AnalyticAffineSpace.polyradius K n m) K) :
    ‖chartRescale K n m f‖ = ‖f‖ :=
  norm_baseChange _ _ _ _ f

theorem chartRescale_injective : Function.Injective (chartRescale K n m) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h := norm_chartRescale K n m f
  rw [hf, norm_zero] at h
  exact norm_eq_zero.mp h.symm

theorem chartRescale_surjective : Function.Surjective (chartRescale K n m) := by
  intro g
  refine ⟨descend (AnalyticAffineSpace.polyradius K n m) (norm_chartScalar K n m)
    (AddMonoidHom.id K) (D := 1) (fun x => le_of_eq (one_mul ‖x‖).symm) g, ?_⟩
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (StrictTateAlgebra.series (Fin n) K (chartRescale K n m _)) =
    MvPowerSeries.coeff d (StrictTateAlgebra.series (Fin n) K g)
  rw [coeff_chartRescale, coeff_descend, AddMonoidHom.id_apply, ← mul_assoc,
    mul_inv_cancel₀ (scale_ne_zero (norm_chartScalar K n m) d), one_mul]

theorem chartRescale_bijective : Function.Bijective (chartRescale K n m) :=
  ⟨chartRescale_injective K n m, chartRescale_surjective K n m⟩

theorem chartRescale_monomial (d : Fin n →₀ ℕ) (a : K) :
    chartRescale K n m (GeneralizedTateAlgebra.monomial (AnalyticAffineSpace.polyradius K n m) K d a) =
      StrictTateAlgebra.monomial (Fin n) K d
        (GeneralizedTateAlgebra.scale (fun _ : Fin n => chartScalar K m) d * a) := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro e
  change MvPowerSeries.coeff e (StrictTateAlgebra.series (Fin n) K (chartRescale K n m _)) =
    MvPowerSeries.coeff e (MvPowerSeries.monomial d _)
  rw [coeff_chartRescale, GeneralizedTateAlgebra.coeff_monomial, MvPowerSeries.coeff_monomial]
  split_ifs with h1 h2 h2
  · subst h1
    rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact mul_zero _

theorem strictMonomial_zero (a : K) :
    StrictTateAlgebra.monomial (Fin n) K 0 a = algebraMap K (StrictTateAlgebra (Fin n) K) a := by
  apply Subtype.ext
  exact MvPowerSeries.monomial_zero_eq_C_apply a

theorem strictMonomial_eq_mul (d : Fin n →₀ ℕ) (a : K) :
    StrictTateAlgebra.monomial (Fin n) K d a =
      algebraMap K (StrictTateAlgebra (Fin n) K) a * StrictTateAlgebra.monomial (Fin n) K d 1 := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro e
  change MvPowerSeries.coeff e (MvPowerSeries.monomial d a) =
    MvPowerSeries.coeff e (MvPowerSeries.C a * MvPowerSeries.monomial d 1)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

omit [IsUltrametricDist K] in
/-- The coordinate rescaling `Tᵢ ↦ a Tᵢ` of the polynomial ring. -/
def polyRescale (a : K) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun i => MvPolynomial.C a * MvPolynomial.X i

omit [IsUltrametricDist K] in
theorem polyRescale_comp (a b : K) :
    (polyRescale K n a).comp (polyRescale K n b) = polyRescale K n (a * b) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, polyRescale, MvPolynomial.aeval_X, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  ring

omit [IsUltrametricDist K] in
theorem polyRescale_one : polyRescale K n 1 = AlgHom.id K (MvPolynomial (Fin n) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polyRescale]

omit [IsUltrametricDist K] in
theorem polyRescale_bijective {a : K} (ha : a ≠ 0) :
    Function.Bijective (polyRescale K n a) := by
  have h1 : (polyRescale K n a).comp (polyRescale K n a⁻¹) =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
    rw [polyRescale_comp, mul_inv_cancel₀ ha, polyRescale_one]
  have h2 : (polyRescale K n a⁻¹).comp (polyRescale K n a) =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
    rw [polyRescale_comp, inv_mul_cancel₀ ha, polyRescale_one]
  refine Function.bijective_iff_has_inverse.mpr ⟨polyRescale K n a⁻¹, fun p => ?_, fun p => ?_⟩
  · exact DFunLike.congr_fun h2 p
  · exact DFunLike.congr_fun h1 p

/-- After rescaling, the weighted polynomial map is the strict polynomial map
precomposed with the coordinate rescaling `Tᵢ ↦ ϖ⁻ᵐ Tᵢ`. -/
theorem chartRescale_comp_polynomialMap :
    (chartRescale K n m).comp
        (GeneralizedTateAlgebra.polynomialMap (AnalyticAffineSpace.polyradius K n m) K).toRingHom =
      (TatePolynomialFlatness.polynomialMap (K := K) n).toRingHom.comp
        (polyRescale K n (chartScalar K m)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change chartRescale K n m (GeneralizedTateAlgebra.polynomialMap _ K (MvPolynomial.C a)) =
      TatePolynomialFlatness.polynomialMap (K := K) n
        (polyRescale K n (chartScalar K m) (MvPolynomial.C a))
    rw [MvPolynomial.C_apply, GeneralizedTateAlgebra.polynomialMap_monomial,
      chartRescale_monomial, ← MvPolynomial.C_apply]
    have hs : GeneralizedTateAlgebra.scale (fun _ : Fin n => chartScalar K m) 0 = 1 := by
      simp [GeneralizedTateAlgebra.scale]
    rw [hs, one_mul, strictMonomial_zero, polyRescale, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, TatePolynomialFlatness.polynomialMap, MvPolynomial.aeval_C]
  · intro i
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change chartRescale K n m (GeneralizedTateAlgebra.polynomialMap _ K (MvPolynomial.X i)) =
      TatePolynomialFlatness.polynomialMap (K := K) n
        (polyRescale K n (chartScalar K m) (MvPolynomial.X i))
    rw [GeneralizedTateAlgebra.polynomialMap, MvPolynomial.aeval_X, chartRescale_monomial]
    have hs : GeneralizedTateAlgebra.scale (fun _ : Fin n => chartScalar K m)
        (Finsupp.single i 1) = chartScalar K m := by
      simp [GeneralizedTateAlgebra.scale]
    rw [hs, mul_one, strictMonomial_eq_mul, polyRescale, MvPolynomial.aeval_X,
      TatePolynomialFlatness.polynomialMap, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rfl

variable [CompleteSpace K]

/-- The polynomial map into the weighted Tate algebra of the `m`-th chart is flat. -/
theorem flat_chartPolynomialMap :
    (GeneralizedTateAlgebra.polynomialMap (AnalyticAffineSpace.polyradius K n m) K).toRingHom.Flat := by
  have h1 : ((TatePolynomialFlatness.polynomialMap (K := K) n).toRingHom.comp
      (polyRescale K n (chartScalar K m)).toRingHom).Flat :=
    (RingHom.Flat.of_bijective (f := (polyRescale K n (chartScalar K m)).toRingHom)
      (polyRescale_bijective K n (chartScalar_ne_zero K m))).comp
      (TatePolynomialFlatness.flat_polynomialMap n)
  rw [← chartRescale_comp_polynomialMap] at h1
  exact (RingHom.Flat.comp_iff_of_bijective_left (chartRescale_bijective K n m)).mp h1

/-- Every ideal of the weighted Tate algebra of the `m`-th chart is closed: the
rescaling is an isometric ring isomorphism onto the Noetherian Banach algebra
`K⟨T₁, …, Tₙ⟩`. -/
theorem isClosed_ideal
    (J : Ideal (GeneralizedTateAlgebra (AnalyticAffineSpace.polyradius K n m) K)) :
    IsClosed (J : Set (GeneralizedTateAlgebra (AnalyticAffineSpace.polyradius K n m) K)) := by
  have hcont : Continuous (chartRescale K n m) :=
    (AddMonoidHomClass.isometry_of_norm (chartRescale K n m) (norm_chartRescale K n m)).continuous
  rw [← Ideal.comap_map_of_bijective (chartRescale K n m) (chartRescale_bijective K n m) (I := J)]
  exact (isClosed_ideal_of_noetherian_banach (K := K) (J.map (chartRescale K n m))).preimage hcont

end Rescale

section Chart

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A) (m : ℕ)

/-- The closed ideal of the `m`-th chart is the extension of the kernel of the
presentation. -/
theorem chart_ideal_eq :
    (PolynomialLocus.chart P (AnalyticAffineSpace.polyradius K P.arity m)).ideal =
      (RingHom.ker P.map.toRingHom).map
        (GeneralizedTateAlgebra.polynomialMap (AnalyticAffineSpace.polyradius K P.arity m) K) := by
  change (Ideal.span (PolynomialLocus.relations P _)).closure = _
  rw [Ideal.closure_eq_of_isClosed _ (isClosed_ideal K P.arity m _)]
  rfl

/-- The algebra map from `A` to the `m`-th chart algebra is flat. -/
theorem flat_chartAlgebraMap :
    (PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity m)).toRingHom.Flat := by
  set r := AnalyticAffineSpace.polyradius K P.arity m
  set ψ := (GeneralizedTateAlgebra.polynomialMap r K).toRingHom with hψ
  set I := RingHom.ker P.map.toRingHom with hI
  let J : Ideal (GeneralizedTateAlgebra r K) := (PolynomialLocus.chart P r).ideal
  have hJ : J = I.map ψ := chart_ideal_eq K P m
  let e : (MvPolynomial (Fin P.arity) K ⧸ I) ≃+* A :=
    P.map.toRingHom.quotientKerEquivOfSurjective P.surjective
  let q : (GeneralizedTateAlgebra r K ⧸ J) ≃+* (GeneralizedTateAlgebra r K ⧸ I.map ψ) :=
    Ideal.quotEquivOfEq hJ
  let α : A →+* GeneralizedTateAlgebra r K ⧸ J := (PolynomialLocus.algebraMap P r).toRingHom
  have hcomp : (q.toRingHom.comp α).comp e.toRingHom =
      Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    change q (α (e (Ideal.Quotient.mk I p))) =
      Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map (Ideal.Quotient.mk I p)
    rw [Ideal.quotientMap_mk]
    have he : e (Ideal.Quotient.mk I p) = P.map p :=
      RingHom.quotientKerEquivOfSurjective_apply_mk P.surjective p
    rw [he]
    change q (PolynomialLocus.algebraMap P r (P.map p)) = _
    rw [PolynomialLocus.algebraMap_map]
    exact Ideal.quotEquivOfEq_mk hJ (ψ p)
  have hflat : ((q.toRingHom.comp α).comp e.toRingHom).Flat := by
    rw [hcomp]
    exact flat_quotientMap ψ (flat_chartPolynomialMap K P.arity m) I
  exact (RingHom.Flat.comp_iff_of_bijective_left (g := q.toRingHom) q.bijective).mp
    ((RingHom.Flat.comp_iff_of_bijective_right (g := e.toRingHom) e.bijective).mp hflat)

end Chart

end ChartFlatness

namespace AffineAnalytification

/-- Berkovich 1990, last paragraph of the proof of Theorem 3.4.1: the algebra maps
from `A` to the chart algebras of its analytification are flat. -/
theorem affineAnalytificationChartFlat : AffineAnalytificationChartFlatStatement.{u, v} := by
  intro K _ _ _ A _ _ P m
  exact ChartFlatness.flat_chartAlgebraMap K P m

end AffineAnalytification

end Langlands.Analytic
