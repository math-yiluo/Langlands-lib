import Langlands.GroupScheme.Rational.MatrixEntryBoundedness
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement

/-! # Polynomial growth of actual regular functions in a closed matrix embedding -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

universe u v w

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A polynomial in coordinates bounded by a height at least one has a
power bound, with its degree and positive constant chosen before all points. -/
theorem polynomial_evaluation_powerBound
    {F : Type u} [NormedField F] {A : Type v} [CommRing A] [Algebra F A]
    {Idx : Type w} {σ : Type*} (e : Idx → A →ₐ[F] F)
    (H : Idx → ℝ) (hH : ∀ i, 1 ≤ H i)
    (f : MvPolynomial σ F →ₐ[F] A)
    (hX : ∀ s i, ‖e i (f (MvPolynomial.X s))‖ ≤ H i)
    (p : MvPolynomial σ F) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ i, ‖e i (f p)‖ ≤ c * H i ^ d := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, ‖c‖ + 1, by positivity, fun i => ?_⟩
      simp only [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, pow_zero, mul_one]
      exact le_add_of_nonneg_right zero_le_one
  | add p q hp hq =>
      obtain ⟨d, c, hc, hp⟩ := hp
      obtain ⟨d', c', hc', hq⟩ := hq
      refine ⟨max d d', c + c', add_pos hc hc', fun i => ?_⟩
      calc
        ‖e i (f (p + q))‖ ≤ ‖e i (f p)‖ + ‖e i (f q)‖ := by
          rw [map_add, map_add]
          exact norm_add_le _ _
        _ ≤ c * H i ^ d + c' * H i ^ d' := add_le_add (hp i) (hq i)
        _ ≤ c * H i ^ max d d' + c' * H i ^ max d d' :=
          add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hH i) (le_max_left _ _)) hc.le)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hH i) (le_max_right _ _)) hc'.le)
        _ = (c + c') * H i ^ max d d' := (add_mul _ _ _).symm
  | mul_X p s hp =>
      obtain ⟨d, c, hc, hp⟩ := hp
      refine ⟨d + 1, c, hc, fun i => ?_⟩
      calc
        ‖e i (f (p * MvPolynomial.X s))‖ =
            ‖e i (f p)‖ * ‖e i (f (MvPolynomial.X s))‖ := by
          rw [map_mul, map_mul, norm_mul]
        _ ≤ (c * H i ^ d) * H i :=
          mul_le_mul (hp i) (hX s i) (norm_nonneg _)
            (mul_nonneg hc.le (pow_nonneg (zero_le_one.trans (hH i)) d))
        _ = c * H i ^ (d + 1) := by rw [pow_succ, mul_assoc]

/-- A surjective polynomial presentation transfers coordinate power bounds to
every element of the actual algebra. -/
theorem algebra_evaluation_powerBound_of_polynomial_surjective
    {F : Type u} [NormedField F] {A : Type v} [CommRing A] [Algebra F A]
    {Idx : Type w} {σ : Type*} (e : Idx → A →ₐ[F] F)
    (H : Idx → ℝ) (hH : ∀ i, 1 ≤ H i)
    (f : MvPolynomial σ F →ₐ[F] A) (hf : Function.Surjective f)
    (hX : ∀ s i, ‖e i (f (MvPolynomial.X s))‖ ≤ H i)
    (a : A) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ i, ‖e i a‖ ≤ c * H i ^ d := by
  obtain ⟨p, rfl⟩ := hf a
  exact polynomial_evaluation_powerBound e H hH f hX p

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.MatrixRepresentation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Polynomial growth of an actual regular function relative to a supplied matrix
representation. The degree and positive constant precede all rational points. -/
def RegularFunctionPolynomialGrowth
    (ρ : MatrixRepresentation G n) (a : AffineCoordinateRing F G.X) : Prop :=
  ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
    LocalField.residueNormalizedAbsoluteValue F (rationalPointAlgebraHom F G.X g a) ≤
      c * rationalMatrixNorm F ρ g ^ d

/-- Every actual regular function is bounded by a fixed power of the actual
rational matrix norm for a closed embedding, over any nonarchimedean local field. -/
theorem regularFunction_rationalMatrixNorm_powerBound
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (a : AffineCoordinateRing F G.X) :
    RegularFunctionPolynomialGrowth F ρ a := by
  unfold RegularFunctionPolynomialGrowth
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (Grp.toMon (GeneralLinear.groupScheme n (CommRingCat.of F))).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of F)
  let π : MvPolynomial (GeneralLinear.Coordinate n) F →ₐ[F]
      AffineCoordinateRing F G.X :=
    (affineCoordinatePullback F ρ.hom.hom).comp
      ((spectrumCoordinateAlgEquiv F (GeneralLinear.CoordinateRing n F)).symm.toAlgHom.comp
        (GeneralLinear.quotient n F))
  have hπ : Function.Surjective π :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2.comp
      ((spectrumCoordinateAlgEquiv F (GeneralLinear.CoordinateRing n F)).symm.surjective.comp
        Ideal.Quotient.mk_surjective)
  have he (g : rationalPoints G) (i j : n) :
      rationalPointAlgebraHom F G.X g (π (MvPolynomial.X (.entry i j))) =
        ρ.rationalMatrix g i j := by
    rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (g.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.entrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((g.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.entrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hi (g : rationalPoints G) (i j : n) :
      rationalPointAlgebraHom F G.X g (π (MvPolynomial.X (.inverseEntry i j))) =
        (ρ.rationalMatrix g)⁻¹ i j := by
    rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_inv_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (g.left.appTop (ρ.hom.hom.left.appTop
        (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom
        ((g.left ≫ ρ.hom.hom.left).appTop
          (GeneralLinear.inverseEntrySection n (CommRingCat.of F) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl
  apply algebra_evaluation_powerBound_of_polynomial_surjective
    (fun g : rationalPoints G => rationalPointAlgebraHom F G.X g)
    (rationalMatrixNorm F ρ) (one_le_rationalMatrixNorm F ρ) π hπ
  intro s g
  cases s with
  | entry i j =>
      rw [he]
      exact HarishChandraSchwartz.norm_le_glNorm (ρ.rationalMatrix g) i j
  | inverseEntry i j =>
      rw [hi]
      exact HarishChandraSchwartz.norm_inv_le_glNorm (ρ.rationalMatrix g) i j

end Langlands.GroupScheme.MatrixRepresentation
