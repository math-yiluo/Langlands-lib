import Langlands.CommutativeAlgebra.MultivariateValuationRegularity
import Langlands.CommutativeAlgebra.FlatUnramifiedProjectiveDimension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat

/-! # Finite projective dimension on etale valuation polynomial charts -/

universe u v w

namespace Langlands.CommutativeAlgebra

open CategoryTheory Module

variable {R : Type u} [CommRing R]

/-- The coefficient-linear map obtained from a polynomial algebra map
and a finite free algebra-module map. -/
noncomputable def polynomialCoefficientModuleMap {S : Type v} [CommRing S] [Algebra R S]
    {k n : ℕ} (p : MvPolynomial (Fin k) R →ₐ[R] S)
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (f : (Fin n → S) →ₗ[S] M) :
    (Fin n → MvPolynomial (Fin k) R) →ₗ[R] M :=
  (f.restrictScalars R).comp
    (LinearMap.pi fun i => p.toLinearMap.comp (LinearMap.proj i))

theorem polynomialCoefficientModuleMap_surjective
    {S : Type v} [CommRing S] [Algebra R S]
    {k n : ℕ} (p : MvPolynomial (Fin k) R →ₐ[R] S)
    (hp : Function.Surjective p)
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (f : (Fin n → S) →ₗ[S] M)
    (hf : Function.Surjective f) :
    Function.Surjective (polynomialCoefficientModuleMap p f) := by
  classical
  intro x
  obtain ⟨y, hy⟩ := hf x
  refine ⟨fun i => Classical.choose (hp (y i)), ?_⟩
  change f (fun i => p (Classical.choose (hp (y i)))) = x
  have h : (fun i => p (Classical.choose (hp (y i)))) = y := by
    funext i
    exact Classical.choose_spec (hp (y i))
  rw [h, hy]

/-- A finite module over a finite-type algebra is countably spanned over
its coefficient ring. -/
theorem countablySpanned_of_finite_finiteType {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] : CountablySpanned R M := by
  obtain ⟨k, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType R S)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  exact (countablySpanned_of_countable_basis (polynomialVectorMonomialBasis (Fin k) n)).of_surjective
    (polynomialCoefficientModuleMap p f) (polynomialCoefficientModuleMap_surjective p hp f hf)

variable [IsDomain R] [ValuationRing R]
variable {σ : Type u} [Finite σ] {S : Type u} [CommRing S]
variable [Algebra R S] [Algebra (MvPolynomial σ R) S]
variable [IsScalarTower R (MvPolynomial σ R) S]

omit [IsScalarTower R (MvPolynomial σ R) S] in
/-- A finite module on a flat unramified finite-type polynomial chart,
torsion-free over the valuation ring, has the polynomial dimension bound. -/
theorem hasProjectiveDimensionLE_of_finite_unramified_mvPolynomial_of_valuationRing
    [Algebra.FiniteType R S] [Module.Flat (MvPolynomial σ R) S]
    [Algebra.EssFiniteType (MvPolynomial σ R) S]
    [Algebra.FormallyUnramified (MvPolynomial σ R) S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [Module S M] [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
    [IsScalarTower (MvPolynomial σ R) S M] [Module.Finite S M]
    [Module.IsTorsionFree R M] :
    HasProjectiveDimensionLE (ModuleCat.of S M) (1 + Nat.card σ) := by
  have : HasProjectiveDimensionLE (ModuleCat.of R M) 1 :=
    hasProjectiveDimensionLE_one_of_countablySpanned_of_valuationRing
      (countablySpanned_of_finite_finiteType (R := R) (S := S) M)
  have : HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ R) M) (1 + Nat.card σ) :=
    mvPolynomialAction_hasProjectiveDimensionLE_of_finite (R := R) (σ := σ) 1 M
  exact hasProjectiveDimensionLE_of_flat_unramified (R := MvPolynomial σ R) (S := S) M _

/-- Every finitely presented module on a flat unramified finite-type
polynomial chart has finite projective dimension. -/
theorem hasProjectiveDimensionLE_of_finitePresentation_unramified_mvPolynomial_of_valuationRing
    [Algebra.FiniteType R S] [Module.Flat (MvPolynomial σ R) S]
    [Algebra.EssFiniteType (MvPolynomial σ R) S]
    [Algebra.FormallyUnramified (MvPolynomial σ R) S]
    (M : Type u) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    HasProjectiveDimensionLE (ModuleCat.of S M) (1 + Nat.card σ + 1) := by
  have : Module.Flat R S := Module.Flat.trans R (MvPolynomial σ R) S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  have : Module.Finite S (LinearMap.ker f) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  have hK := hasProjectiveDimensionLE_of_finite_unramified_mvPolynomial_of_valuationRing
    (R := R) (σ := σ) (S := S) (LinearMap.ker f)
  have hF : HasProjectiveDimensionLT (ModuleCat.of S (Fin n → S))
      (1 + Nat.card σ + 1 + 1) := inferInstance
  exact (LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃
    (1 + Nat.card σ + 1) hK hF

/-- The finite-projective-dimension predicate holds on every etale polynomial
chart over an arbitrary valuation domain. -/
theorem finiteProjectiveDimensionForFinitelyPresentedModules_etale_mvPolynomial_of_valuationRing
    [Algebra.Etale (MvPolynomial σ R) S] :
    FiniteProjectiveDimensionForFinitelyPresentedModules S := by
  have : Algebra.FiniteType R S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R (MvPolynomial σ R))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ R) S)
  intro M _ _ _
  exact ⟨1 + Nat.card σ + 1,
    hasProjectiveDimensionLE_of_finitePresentation_unramified_mvPolynomial_of_valuationRing
      (R := R) (σ := σ) M⟩

end Langlands.CommutativeAlgebra
