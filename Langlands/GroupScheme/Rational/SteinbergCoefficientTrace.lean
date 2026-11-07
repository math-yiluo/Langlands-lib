import Langlands.GroupScheme.Rational.SteinbergPolynomialAction
import Langlands.GroupScheme.Rational.SteinbergWeightPaths
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Mathlib.LinearAlgebra.Trace

/-! # Coefficient expansion and trace support for actual Steinberg products -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped BigOperators Matrix

namespace Langlands.GroupScheme.SplitPinning

private theorem ofFn_prod_sum {S : Type*} [Semiring S]
    (r : ℕ) (a : Fin r → Type*) [∀ j, Fintype (a j)] (f : ∀ j, a j → S) :
    (List.ofFn fun j => ∑ m, f j m).prod =
      ∑ m : ∀ j, a j, (List.ofFn fun j => f j (m j)).prod := by
  classical
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons,
      ih (fun j => a j.succ) (fun j => f j.succ)]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have h := (Fin.consEquiv a).sum_comp
      (fun m => (List.ofFn fun j => f j (m j)).prod)
    rw [Fintype.sum_prod_type] at h
    simpa only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ,
      List.prod_cons, Fin.cons_zero, Fin.cons_succ] using h

private theorem ofFn_prod_smul_map {K A : Type*} [CommRing K] [CommRing A]
    {n : Type} [Fintype n] [DecidableEq n] (f : K →+* A)
    (r : ℕ) (c : Fin r → A) (M : Fin r → Matrix n n K) :
    (List.ofFn fun j => c j • (M j).map f).prod =
      (∏ j, c j) • ((List.ofFn M).prod.map f) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, ih]
    rw [List.ofFn_succ, List.prod_cons, Matrix.map_mul,
      Fin.prod_univ_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- The finite tuples of root degrees occurring in the actual matrix expansion. -/
abbrev steinbergCoefficientDegrees : Type :=
  ∀ j : Fin r, Fin (degreeBound (ρ.restrict (x (e j)).hom))

private theorem steinbergPolynomialFactor_eq_sum (j : Fin r) :
    ((univariateMatrix (ρ.restrict (x (e j)).hom)).map
        (Polynomial.aeval (MvPolynomial.X j))) *
      ((ρ.rationalMatrix (s (e j)).point : Matrix n n k).map MvPolynomial.C) =
      ∑ m : Fin (degreeBound (ρ.restrict (x (e j)).hom)),
        ((MvPolynomial.X j : MvPolynomial (Fin r) k) ^ (m : ℕ)) •
          ((coefficientMatrix (ρ.restrict (x (e j)).hom) m *
            (ρ.rationalMatrix (s (e j)).point : Matrix n n k)).map MvPolynomial.C) := by
  have h := affineMatrix_eq_sum (ρ.restrict (x (e j)).hom)
    (VectorGroup.coordinateAlgebra (CommRingCat.of k) r) (MvPolynomial.X j)
  rw [← univariateMatrix_aeval (ρ.restrict (x (e j)).hom)
    (VectorGroup.coordinateAlgebra (CommRingCat.of k) r) (MvPolynomial.X j)] at h
  rw [h, Finset.sum_mul, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dite_eq_left (Finset.mem_range.mp hm), Matrix.smul_mul, Matrix.map_mul]
  rfl

/-- The actual polynomial matrix is the finite monomial expansion of the
ordered actual coefficient matrices. -/
theorem steinbergPolynomialMatrix_eq_sum_coefficients :
    steinbergPolynomialMatrix e x s ρ =
      ∑ m : steinbergCoefficientDegrees e x ρ,
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin r) k) ^ (m j : ℕ)) •
          (steinbergCoefficientMatrix x s ρ e (fun j => m j)).map MvPolynomial.C := by
  classical
  calc
    _ = (List.ofFn fun j =>
          ∑ m : Fin (degreeBound (ρ.restrict (x (e j)).hom)),
            ((MvPolynomial.X j : MvPolynomial (Fin r) k) ^ (m : ℕ)) •
              ((coefficientMatrix (ρ.restrict (x (e j)).hom) m *
                (ρ.rationalMatrix (s (e j)).point : Matrix n n k)).map MvPolynomial.C)).prod := by
      apply congrArg List.prod
      apply congrArg List.ofFn
      funext j
      exact steinbergPolynomialFactor_eq_sum e x s ρ j
    _ = _ := by
      rw [ofFn_prod_sum]
      apply Finset.sum_congr rfl
      intro m hm
      exact ofFn_prod_smul_map _ r _ _

/-- Restriction of the actual invariant trace has the same finite expansion. -/
theorem steinbergRestriction_trace_eq_sum_coefficients :
    steinbergRestriction e x s ρ.traceClassFunction =
      ∑ m : steinbergCoefficientDegrees e x ρ,
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin r) k) ^ (m j : ℕ)) *
          MvPolynomial.C (Matrix.trace
            (steinbergCoefficientMatrix x s ρ e (fun j => m j))) := by
  rw [steinbergRestriction_traceClassFunction, steinbergPolynomialMatrix_eq_sum_coefficients,
    Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Matrix.trace_smul, ← AddMonoidHom.map_trace MvPolynomial.C, smul_eq_mul]

/-- A split maximal torus admits a basis of actual all-algebra weight vectors. -/
theorem exists_representationWeightBasis :
    ∃ (b : Basis n k (n → k)) (lam : n → characterLattice p.torus),
      ∀ j, b j ∈ p.representationWeightSpace ρ (lam j) := by
  let := p.isSplitTorus.isAffineHom
  obtain ⟨b, χ, hb⟩ := MatrixRepresentation.exists_characterBasis
    (ρ.restrict p.inclusion)
    (MatrixRepresentation.iSup_characterSpace_eq_top_of_isSplitTorus
      p.isSplitTorus (ρ.restrict p.inclusion))
  refine ⟨b, fun j => rationalCharacters.equivCharacterLattice p.torus (χ j), ?_⟩
  intro j
  simpa only [representationWeightSpace, AddEquiv.symm_apply_apply] using hb j

/-- Projection onto a basis vector's weight preserves its coordinate. -/
theorem weightBasis_coord_representationWeightProjector
    (b : Basis n k (n → k)) (lam : n → characterLattice p.torus)
    (hb : ∀ j, b j ∈ p.representationWeightSpace ρ (lam j)) (i : n) (v : n → k) :
    b.coord i (p.representationWeightProjector ρ (lam i) v) = b.coord i v := by
  classical
  let := p.isSplitTorus.isAffineHom
  suffices h : (b.coord i).comp (p.representationWeightProjector ρ (lam i)) =
      b.coord i from LinearMap.congr_fun h v
  apply b.ext
  intro j
  have hp := (ρ.restrict p.inclusion).characterProjector_of_mem
    ((rationalCharacters.equivCharacterLattice p.torus).symm (lam i))
    ((rationalCharacters.equivCharacterLattice p.torus).symm (lam j)) (hb j)
  change p.representationWeightProjector ρ (lam i) (b j) = _ at hp
  simp only [EquivLike.apply_eq_iff_eq] at hp
  rw [LinearMap.comp_apply, hp]
  split_ifs with h
  · rfl
  · have hji : j ≠ i := fun hji => h (congrArg lam hji)
    simp [Basis.coord_apply, hji]

/-- Without an occurring weight of the prescribed simple-coroot degrees,
the actual ordered coefficient matrix has zero trace. -/
theorem steinbergCoefficientMatrix_trace_eq_zero_of_no_weight (m : Fin r → ℕ)
    (h : ∀ lam : characterLattice p.torus,
      p.representationWeightSpace ρ lam ≠ ⊥ →
        ¬ ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j))) :
    Matrix.trace (steinbergCoefficientMatrix x s ρ e m) = 0 := by
  classical
  obtain ⟨b, lam, hb⟩ := exists_representationWeightBasis ρ
  have hd (j : n) :
      b.coord j (steinbergCoefficientMatrix x s ρ e m *ᵥ b j) = 0 := by
    have hn : p.representationWeightSpace ρ (lam j) ≠ ⊥ := by
      intro hz
      have hm := hb j
      rw [hz, Submodule.mem_bot] at hm
      exact b.ne_zero j hm
    have hp := representationWeightProjector_steinbergCoefficient e x s ρ m (hb j)
    rw [ite_eq_right (h (lam j) hn)] at hp
    have hc := congrArg (b.coord j) hp
    rw [weightBasis_coord_representationWeightProjector ρ b lam hb] at hc
    exact hc.trans (map_zero _)
  rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Matrix.toLin'_apply]
  exact Finset.sum_eq_zero (fun j _ => hd j)

/-- A nonzero coefficient trace witnesses an occurring dominant weight whose
simple-coroot pairings are exactly the coefficient degrees. -/
theorem exists_dominant_weight_of_steinbergCoefficientMatrix_trace_ne_zero
    (m : Fin r → ℕ)
    (htrace : Matrix.trace (steinbergCoefficientMatrix x s ρ e m) ≠ 0) :
    ∃ lam : characterLattice p.torus,
      p.representationWeightSpace ρ lam ≠ ⊥ ∧ p.IsDominantWeight lam ∧
        ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j)) := by
  classical
  by_contra h
  apply htrace
  apply steinbergCoefficientMatrix_trace_eq_zero_of_no_weight e x s ρ m
  intro lam hmem hm
  apply h
  exact ⟨lam, hmem,
    isDominantWeight_of_coefficientWeightPath_closed e m lam
      ((coefficientWeightPath_closed_iff e m lam).mpr hm), hm⟩

end Langlands.GroupScheme.SplitPinning
