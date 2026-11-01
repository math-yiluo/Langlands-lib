import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentGaussSection
import Langlands.Geometry.Analytic.Spectrum.JointContinuityProof
import Mathlib.Topology.Order.Lattice

/-! # Continuity of the relative Laurent Gauss section -/

noncomputable section

universe u

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra
open Filter Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (t : ℝ) [Fact (0 < t)]

/-- The imposed equation makes the two new quotient coordinates inverse. -/
theorem coordinate_mul :
    Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 0 *
      Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 1 = 1 := by
  have h := Adjoin.presentationMap_equation K A (LaurentAnnulus.radii t)
    {relation K A t} (Set.mem_singleton (relation K A t))
  change Ideal.Quotient.mk
    ((Ideal.span (Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t})).closure)
    (relation K A t) = 0 at h
  unfold relation at h
  rw [map_sub, map_mul, map_one, sub_eq_zero] at h
  exact h

/-- The actual Laurent variable in the relative closed quotient. -/
def coordinateUnit : (algebra K A t)ˣ :=
  ⟨Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 0,
    Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 1,
    coordinate_mul K A t, by rw [mul_comm]; exact coordinate_mul K A t⟩

/-- Finite Laurent expressions with coefficients in the original affinoid algebra. -/
def polynomialMap : AddMonoidAlgebra A ℤ →+* algebra K A t :=
  AddMonoidAlgebra.liftNCRingHom (baseMap K A t).toAlgHom.toRingHom
    (GaussLaurent.unitPowers (algebra K A t) (coordinateUnit K A t))
    (fun _ _ => Commute.all _ _)

@[simp] theorem polynomialMap_single (n : ℤ) (a : A) :
    polynomialMap K A t (AddMonoidAlgebra.single n a) =
      baseMap K A t a * (↑((coordinateUnit K A t) ^ n) : algebra K A t) :=
  AddMonoidAlgebra.liftNCRingHom_single _ _ _ n a

/-- Constant Laurent expressions contain the whole original algebra. -/
theorem baseMap_mem_polynomialMap_range (a : A) :
    baseMap K A t a ∈ (polynomialMap K A t).range := by
  refine ⟨AddMonoidAlgebra.single 0 a, ?_⟩
  rw [polynomialMap_single]
  simp

/-- Every coordinate of the enlarged scalar presentation is a finite Laurent expression. -/
theorem coordinate_mem_polynomialMap_range (i : Fin (A.arity + 2)) :
    coordinate K (algebra K A t) i ∈ (polynomialMap K A t).range := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [← Adjoin.baseMap_coordinate K A (LaurentAnnulus.radii t) {relation K A t} j]
    exact baseMap_mem_polynomialMap_range K A t (coordinate K A j)
  · intro j
    fin_cases j
    · refine ⟨AddMonoidAlgebra.single 1 1, ?_⟩
      rw [polynomialMap_single]
      simp [coordinateUnit, Adjoin.newCoordinate]
    · refine ⟨AddMonoidAlgebra.single (-1) 1, ?_⟩
      rw [polynomialMap_single]
      simp [coordinateUnit, Adjoin.newCoordinate]

/-- Scalar polynomials in every presentation coordinate have finite Laurent images. -/
theorem presentation_polynomial_mem_range
    (p : MvPolynomial (Fin (algebra K A t).arity) K) :
    presentationMap K (algebra K A t)
      (GeneralizedTateAlgebra.polynomialMap (algebra K A t).polyradius K p) ∈
      (polynomialMap K A t).range := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [GeneralizedTateAlgebra.polynomialMap, MvPolynomial.aeval_C,
      AlgHom.commutes]
    simpa only [← AlgHom.commutes (baseMap K A t).toAlgHom] using
      baseMap_mem_polynomialMap_range K A t (algebraMap K A a)
  | add p q hp hq =>
    rw [map_add, map_add]
    exact (polynomialMap K A t).range.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    apply (polynomialMap K A t).range.mul_mem hp
    rw [GeneralizedTateAlgebra.polynomialMap, MvPolynomial.aeval_X]
    change coordinate K (algebra K A t) i ∈ (polynomialMap K A t).range
    exact coordinate_mem_polynomialMap_range K A t i

/-- Finite Laurent expressions are dense in the actual closed-relation quotient. -/
theorem denseRange_polynomialMap : DenseRange (polynomialMap K A t) := by
  have hd := (presentationMap_surjective K (algebra K A t)).denseRange.comp
    (GeneralizedTateAlgebra.denseRange_polynomialMap
      (algebra K A t).polyradius K)
    (presentationMap K (algebra K A t)).continuous
  exact hd.mono (by
    rintro _ ⟨p, rfl⟩
    exact presentation_polynomial_mem_range K A t p)

variable [CompleteSpace K]

@[simp] theorem evaluation_newCoordinate (x : BanachSpectrum A) (i : Fin 2) :
    evaluation K A t x
      (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} i) =
      LaurentAnnulus.completionTuple (BanachSpectrum.CompletedResidueField K x) t i :=
  seriesEvaluation_newX K A t x i

/-- Evaluation respects the Laurent variable as a unit, and therefore all integer powers. -/
theorem evaluation_coordinateUnit (x : BanachSpectrum A) :
    Units.map (evaluation K A t x).toAlgHom.toRingHom.toMonoidHom (coordinateUnit K A t) =
      (CompletedGaussLaurent.variableUnit : (Fiber K A t x)ˣ) := by
  apply Units.ext
  exact evaluation_newCoordinate K A t x 0

/-- Apply the actual completed residue map to the finite Laurent coefficients. -/
def residuePolynomial (x : BanachSpectrum A) :
    AddMonoidAlgebra A ℤ →+* GaussLaurent (BanachSpectrum.CompletedResidueField K x) t :=
  AddMonoidAlgebra.mapRingHom ℤ (BanachSpectrum.completedResidueMap K x).toAlgHom.toRingHom

omit [Fact (0 < t)] [CompleteSpace K] in
@[simp] theorem residuePolynomial_coeff (x : BanachSpectrum A)
    (p : AddMonoidAlgebra A ℤ) (n : ℤ) :
    GaussLaurent.coeff (residuePolynomial K A t x p) n =
      BanachSpectrum.completedResidueMap K x (p.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom _ p n

omit [CompleteSpace K] in
@[simp] theorem norm_completedResidueMap (x : BanachSpectrum A) (a : A) :
    ‖BanachSpectrum.completedResidueMap K x a‖ = x a := by
  change ‖(BanachSpectrum.residueFieldMap K x a :
    BanachSpectrum.CompletedResidueField K x)‖ = x a
  rw [UniformSpace.Completion.norm_coe, BanachSpectrum.norm_residueFieldMap]

/-- Evaluation of a finite expression is exactly its coefficientwise residue polynomial. -/
theorem evaluation_polynomialMap (x : BanachSpectrum A) (p : AddMonoidAlgebra A ℤ) :
    evaluation K A t x (polynomialMap K A t p) =
      ((residuePolynomial K A t x p :
        GaussLaurent (BanachSpectrum.CompletedResidueField K x) t) :
        CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t) := by
  let ev : algebra K A t →+*
      CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t :=
    (evaluation K A t x).toAlgHom.toRingHom
  change ev (polynomialMap K A t p) = _
  have hbase (a : A) : ev (baseMap K A t a) =
      CompletedGaussLaurent.ι (t := t) (BanachSpectrum.completedResidueMap K x a) :=
    evaluation_baseMap K A t x a
  have hpow (n : ℤ) : ev (↑((coordinateUnit K A t) ^ n) : algebra K A t) =
      (↑((CompletedGaussLaurent.variableUnit :
        (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)ˣ) ^ n) :
        CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t) := by
    have hn := congrArg (fun b : (Fiber K A t x)ˣ => (↑(b ^ n) : Fiber K A t x))
      (evaluation_coordinateUnit K A t x)
    rw [← map_zpow, Units.coe_map] at hn
    exact hn
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, UniformSpace.Completion.coe_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, UniformSpace.Completion.coe_add]
  | single n a =>
    have hr : residuePolynomial K A t x (AddMonoidAlgebra.single n a) =
        GaussLaurent.single n (BanachSpectrum.completedResidueMap K x a) :=
      AddMonoidAlgebra.mapRingHom_single _ n a
    rw [polynomialMap_single, map_mul, hbase, hpow, hr,
      CompletedGaussLaurent.ι_apply, CompletedGaussLaurent.variableUnit_zpow_val,
      ← UniformSpace.Completion.coe_mul, GaussLaurent.single_mul_single, zero_add, mul_one]

/-- The finite norm formula uses a fixed support, independent of the spectrum point. -/
theorem sectionPoint_polynomialMap (x : BanachSpectrum A) (p : AddMonoidAlgebra A ℤ) :
    sectionPoint K A t x (polynomialMap K A t p) =
      ((p.coeff.support.sup fun n =>
        Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n : NNReal) : ℝ) := by
  classical
  have hcoeff (n : ℤ) :
      ‖GaussLaurent.coeff (residuePolynomial K A t x p) n‖₊ =
        Real.toNNReal (x (p.coeff n)) := by
    apply NNReal.eq
    rw [coe_nnnorm, residuePolynomial_coeff, norm_completedResidueMap,
      Real.coe_toNNReal _ (apply_nonneg x.toMulRingSeminorm _)]
  have hnorm : GaussLaurent.gaussNNNorm (residuePolynomial K A t x p) =
      p.coeff.support.sup (fun n =>
        Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n) := by
    apply le_antisymm
    · rw [GaussLaurent.gaussNNNorm_le_iff]
      intro n
      rw [hcoeff]
      by_cases hn : n ∈ p.coeff.support
      · exact Finset.le_sup (f := fun n =>
          Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n) hn
      · rw [Finsupp.notMem_support_iff.mp hn]
        simp only [map_zero, Real.toNNReal_zero, zero_mul]
        exact zero_le
    · apply Finset.sup_le
      intro n _
      rw [← hcoeff]
      exact GaussLaurent.le_gaussNNNorm _ n
  rw [sectionPoint_apply]
  calc
    _ = ‖((residuePolynomial K A t x p) :
        CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)‖ :=
      congrArg (fun z : CompletedGaussLaurent
        (BanachSpectrum.CompletedResidueField K x) t => ‖z‖)
        (evaluation_polynomialMap K A t x p)
    _ = ‖residuePolynomial K A t x p‖ := UniformSpace.Completion.norm_coe _
    _ = _ := by rw [GaussLaurent.norm_def, hnorm]

/-- Every finite Laurent expression has continuous Gauss evaluation on the base spectrum. -/
theorem continuous_sectionPoint_polynomialMap (p : AddMonoidAlgebra A ℤ) :
    Continuous (fun x : BanachSpectrum A =>
      sectionPoint K A t x (polynomialMap K A t p)) := by
  classical
  simp_rw [sectionPoint_polynomialMap]
  apply NNReal.continuous_coe.comp
  apply Continuous.finset_sup_apply
  intro n _
  exact (continuous_real_toNNReal.comp
    (BanachSpectrum.evaluation (p.coeff n)).continuous).mul continuous_const

/-- Polynomial approximation is uniform in the base spectrum point. -/
theorem sectionPoint_dist_le (x : BanachSpectrum A) (b c : algebra K A t) :
    dist (sectionPoint K A t x b) (sectionPoint K A t x c) ≤ dist b c := by
  rw [Real.dist_eq, dist_eq_norm]
  exact BanachSpectrum.abs_sub_le_norm_sub (sectionPoint K A t x) b c

/-- Evaluation of the section on every actual quotient element is continuous. -/
theorem continuous_sectionPoint_apply (b : algebra K A t) :
    Continuous (fun x : BanachSpectrum A => sectionPoint K A t x b) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨p, hp⟩ := (denseRange_polynomialMap K A t).exists_dist_lt b hthird
  have hevent := Metric.continuousAt_iff'.mp
    ((continuous_sectionPoint_polynomialMap K A t p).continuousAt (x := x))
    (ε / 3) hthird
  filter_upwards [hevent] with y hy
  have happrox (z : BanachSpectrum A) :
      dist (sectionPoint K A t z b)
        (sectionPoint K A t z (polynomialMap K A t p)) < ε / 3 :=
    lt_of_le_of_lt (sectionPoint_dist_le K A t z b (polynomialMap K A t p)) hp
  have hx := happrox x
  have hy' := happrox y
  have htri := dist_triangle4 (sectionPoint K A t y b)
    (sectionPoint K A t y (polynomialMap K A t p))
    (sectionPoint K A t x (polynomialMap K A t p)) (sectionPoint K A t x b)
  rw [dist_comm (sectionPoint K A t x (polynomialMap K A t p))] at htri
  linarith

/-- The actual Gauss section is continuous in the pointwise spectrum topology. -/
theorem continuous_sectionPoint : Continuous (sectionPoint K A t) :=
  continuous_induced_rng.mpr <| continuous_pi fun b => continuous_sectionPoint_apply K A t b

/-- The continuous Gauss section of restriction from the actual relative annulus. -/
def gaussSection : C(BanachSpectrum A, BanachSpectrum (algebra K A t)) :=
  ⟨sectionPoint K A t, continuous_sectionPoint K A t⟩

@[simp] theorem gaussSection_apply (x : BanachSpectrum A) :
    gaussSection K A t x = sectionPoint K A t x := rfl

@[simp] theorem restriction_gaussSection (x : BanachSpectrum A) :
    restriction K A t (gaussSection K A t x) = x :=
  restriction_sectionPoint K A t x

end Langlands.Analytic.RelativeLaurentAnnulus
