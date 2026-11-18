import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroReduction
import Langlands.AbelianScheme.GeometricTraceReduction

/-! # Geometric trace comparison from degree lines and Tate determinant norms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Algebra.DegreeDeterminant

private theorem map_line_eq_charpoly {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime]
    {g : ℕ} {ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]}
    {δ : R → ℚ} {iso : R → Prop} (hD : DegreeData ρ δ iso) (α : R)
    (P : Polynomial ℚ) (hP : ∀ n : ℕ, δ (n • 1 + -α) = P.eval (n : ℚ)) :
    P.map (algebraMap ℚ ℚ_[p]) = (ρ α).charpoly := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℚ_[p]))).mono ?_
  rintro _ ⟨n, rfl⟩
  change (P.map (algebraMap ℚ ℚ_[p])).eval (n : ℚ_[p]) =
    (ρ α).charpoly.eval (n : ℚ_[p])
  calc
    _ = algebraMap ℚ ℚ_[p] (P.eval (n : ℚ)) := by
      simpa only [map_natCast] using
        (Polynomial.eval_map_apply (p := P) (algebraMap ℚ ℚ_[p]) (n : ℚ))
    _ = (δ (n • 1 + -α) : ℚ_[p]) := by rw [hP n]; rfl
    _ = (ρ (n • 1 + -α)).det := hD.det_eq _
    _ = (ρ α).charpoly.eval (n : ℚ_[p]) := by
      rw [Matrix.eval_charpoly, map_add, map_nsmul, map_one, map_neg]
      congr 1
      simp [nsmul_eq_mul, sub_eq_add_neg]

end Langlands.Algebra.DegreeDeterminant

namespace Langlands.AbelianScheme

open Rosati.MumfordTraceReduction Langlands.Algebra.DegreeDeterminant

/-- Degree polynomiality on actual endomorphism lines and the actual Tate determinant
norm comparison imply the full geometric trace comparison in the same universe. -/
def GeometricDegreeTraceReductionStatement : Prop :=
  EndomorphismDegreeLinePolynomialStatement.{u} →
    IsogenyDegreeTateDeterminantNormStatement.{u} →
      GeometricEndomorphismTraceComparisonStatement.{u}

/-- The common rational degree line is the characteristic polynomial at every prime;
its next coefficient gives the common integral trace. -/
theorem geometricDegreeTraceReduction : GeometricDegreeTraceReductionStatement.{u} := by
  intro hG1 hG23
  apply GeometricTrace.comparison_of_integral
  intro k _ _ _ A f
  obtain ⟨g, hA⟩ := exists_hasRelativeDimension_of_field A
  obtain ⟨δ, hδiso, hδline⟩ := hG1 k A g hA
  obtain ⟨P, -, hP⟩ := hδline (𝟙 A) (-f)
  refine ⟨-P.nextCoeff, ?_⟩
  intro p _
  have hp : IsUnit ((p : ℕ) : Γ(Spec (CommRingCat.of k), ⊤)) := by
    simpa using isUnit_intCast_global (k := k) (p : ℤ)
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨-, hfin, hrank⟩ := Tate.PrimeAdic.geometricPrimeAdicRank _ A g hA p hp k (𝟙 _)
  let b := Module.finBasisOfFinrankEq ℚ_[p] _ hrank
  let Vp : End A →+* Module.End ℚ_[p]
      (Tate.PrimeAdic.Rational A (Over.mk (𝟙 (Spec (CommRingCat.of k)))) p) :=
    (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A).toRingHom.comp (endToEnd0 A)
  have hVp : ∀ β : A ⟶ A, Vp β = Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p β :=
    fun β => rationalEndAction_homToHom0 A p β
  let ρ : End A →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p] :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp Vp
  have hdet : ∀ β : A ⟶ A,
      (ρ β).det = LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p β) := by
    intro β
    rw [← hVp β]
    exact LinearMap.det_toMatrix b (Vp β)
  obtain ⟨y₀⟩ := nonempty_left A
  have hD : DegreeData ρ δ (fun β : End A => IsIsogeny (β : A ⟶ A)) :=
    { line := fun φ ψ => hδline φ ψ
      mul := by
        intro β γ hβ hγ
        change δ (γ ≫ β) = δ β * δ γ
        rw [hδiso _ (hγ.comp hβ) y₀, hδiso β hβ y₀, hδiso γ hγ y₀,
          finrank_comp_of_isIsogeny γ β hγ hβ ((hom γ).finrank y₀)
            (fun y => finrank_eq_of_isIsogeny γ hγ y y₀) y₀ y₀]
        push_cast
        ring
      norm := by
        intro β hβ
        rw [hdet, hδiso β hβ y₀]
        push_cast
        exact (hG23 k A p β).1 hβ y₀
      zero := by
        intro β hβ
        rw [hdet]
        exact (hG23 k A p β).2 hβ }
  have hchar : P.map (algebraMap ℚ ℚ_[p]) = (ρ f).charpoly :=
    map_line_eq_charpoly hD f P hP
  change algebraMap ℚ ℚ_[p] (-P.nextCoeff) = LinearMap.trace ℚ_[p] _ (Vp f)
  rw [LinearMap.trace_eq_matrix_trace ℚ_[p] b, Matrix.trace_eq_neg_charpoly_nextCoeff]
  change algebraMap ℚ ℚ_[p] (-P.nextCoeff) = -(ρ f).charpoly.nextCoeff
  rw [← hchar, Polynomial.nextCoeff_map (algebraMap ℚ ℚ_[p]).injective, map_neg]

end Langlands.AbelianScheme
