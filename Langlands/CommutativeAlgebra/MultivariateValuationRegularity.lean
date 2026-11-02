import Langlands.CommutativeAlgebra.HomogenizedPolynomialKernels
import Langlands.CommutativeAlgebra.CountableValuationProjectiveDimension
import Langlands.CommutativeAlgebra.CoherentRegularLocalization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Data.Finsupp.Encodable
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Finite projective dimension over valuation polynomial rings -/

universe u v w

namespace Langlands.CommutativeAlgebra

open CategoryTheory Module Polynomial

variable {R : Type u} [CommRing R]

/-- The coordinate-monomial basis of a finite polynomial-vector module. -/
noncomputable def polynomialVectorMonomialBasis (σ : Type v) (n : ℕ) :
    Basis (Σ _ : Fin n, σ →₀ ℕ) R (Fin n → MvPolynomial σ R) :=
  (Finsupp.basis (fun _ : Fin n => MvPolynomial.basisMonomials σ R)).map
    (Finsupp.linearEquivFunOnFinite R (MvPolynomial σ R) (Fin n))

/-- A finite module over a polynomial ring in finitely many variables is
countably spanned over its coefficient ring. -/
theorem countablySpanned_of_finite_mvPolynomial {σ : Type v} [Finite σ]
    (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M] :
    CountablySpanned R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (MvPolynomial σ R) M
  exact (countablySpanned_of_countable_basis (polynomialVectorMonomialBasis σ n)).of_surjective
    (f.restrictScalars R) hf

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A polynomial action in `k` variables raises an underlying coefficient-ring
projective-dimension bound by at most `k`. -/
theorem mvPolynomialAction_hasProjectiveDimensionLE [Small.{w} R] (k d : ℕ)
    (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin k) R) M]
    [IsScalarTower R (MvPolynomial (Fin k) R) M]
    [HasProjectiveDimensionLE (ModuleCat.of R M) d] :
    HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial (Fin k) R) M) (d + k) := by
  induction k generalizing M with
  | zero =>
    let e := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
    let eM : (ModuleCat.of R M) ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv]
        (ModuleCat.of (MvPolynomial (Fin 0) R) M) :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change r • x = e r • x
          rw [show e r = algebraMap R (MvPolynomial (Fin 0) R) r from e.commutes r]
          exact (IsScalarTower.algebraMap_smul (MvPolynomial (Fin 0) R) r x).symm }
    simpa using ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e.toRingEquiv eM d
  | succ k ih =>
    let e := MvPolynomial.finSuccEquiv R k
    have : Small.{w} (MvPolynomial (Fin k) R)[X] := small_map e.symm.toEquiv
    let : Module (MvPolynomial (Fin k) R)[X] M := Module.compHom M e.symm.toRingHom
    let : Module (MvPolynomial (Fin k) R) M :=
      Module.compHom M (e.symm.toRingHom.comp Polynomial.C)
    have : IsScalarTower (MvPolynomial (Fin k) R) (MvPolynomial (Fin k) R)[X] M :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R (MvPolynomial (Fin k) R) M :=
      IsScalarTower.of_algebraMap_smul fun r x => by
        change e.symm (Polynomial.C (MvPolynomial.C r)) • x = r • x
        rw [show e.symm (Polynomial.C (MvPolynomial.C r)) =
          algebraMap R (MvPolynomial (Fin (k + 1)) R) r from e.symm.commutes r]
        exact IsScalarTower.algebraMap_smul (MvPolynomial (Fin (k + 1)) R) r x
    have := ih M
    have := polynomialAction_hasProjectiveDimensionLE (R := MvPolynomial (Fin k) R) (d + k) M
    let eM : (ModuleCat.of (MvPolynomial (Fin k) R)[X] M) ≃ₛₗ[RingHomClass.toRingHom e.symm.toRingEquiv]
        (ModuleCat.of (MvPolynomial (Fin (k + 1)) R) M) :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    simpa only [Nat.add_assoc] using
      ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e.symm.toRingEquiv eM (d + k + 1)

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- The action bound for any finite variable type, with no chosen enumeration. -/
theorem mvPolynomialAction_hasProjectiveDimensionLE_of_finite [Small.{w} R]
    {σ : Type v} [Finite σ] (d : ℕ)
    (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    [HasProjectiveDimensionLE (ModuleCat.of R M) d] :
    HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ R) M) (d + Nat.card σ) := by
  let e := MvPolynomial.renameEquiv R (Finite.equivFin σ).symm
  let : Module (MvPolynomial (Fin (Nat.card σ)) R) M := Module.compHom M e.toRingHom
  have : IsScalarTower R (MvPolynomial (Fin (Nat.card σ)) R) M :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change e (MvPolynomial.C r) • x = r • x
      rw [show e (MvPolynomial.C r) = algebraMap R (MvPolynomial σ R) r from e.commutes r]
      exact IsScalarTower.algebraMap_smul (MvPolynomial σ R) r x
  have := mvPolynomialAction_hasProjectiveDimensionLE (R := R) (Nat.card σ) d M
  let eM : (ModuleCat.of (MvPolynomial (Fin (Nat.card σ)) R) M)
      ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv] (ModuleCat.of (MvPolynomial σ R) M) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e.toRingEquiv eM _

/-- A finite polynomial module torsion-free over its valuation coefficient ring
has projective dimension at most the number of variables plus one. -/
theorem hasProjectiveDimensionLE_of_finite_mvPolynomial_of_valuationRing
    [Small.{w} R] [IsDomain R] [ValuationRing R]
    {σ : Type v} [Finite σ]
    (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M]
    [Module.IsTorsionFree R M] :
    HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ R) M) (1 + Nat.card σ) := by
  have := hasProjectiveDimensionLE_one_of_countablySpanned_of_valuationRing
    (countablySpanned_of_finite_mvPolynomial (R := R) (σ := σ) M)
  exact mvPolynomialAction_hasProjectiveDimensionLE_of_finite (R := R) (σ := σ) 1 M

/-- Finitely presented modules over a finite-variable valuation polynomial ring
have projective dimension at most the number of variables plus two. -/
theorem hasProjectiveDimensionLE_of_finitePresentation_mvPolynomial_of_valuationRing
    [IsDomain R] [ValuationRing R] {σ : Type v} [Finite σ]
    (M : Type (max u v)) [AddCommGroup M] [Module (MvPolynomial σ R) M]
    [Module.FinitePresentation (MvPolynomial σ R) M] :
    HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial σ R) M) (1 + Nat.card σ + 1) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (MvPolynomial σ R) M
  have : Module.Finite (MvPolynomial σ R) (LinearMap.ker f) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  have hK := hasProjectiveDimensionLE_of_finite_mvPolynomial_of_valuationRing
    (R := R) (σ := σ) (LinearMap.ker f)
  have hF : HasProjectiveDimensionLT
      (ModuleCat.of (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
      (1 + Nat.card σ + 1 + 1) := inferInstance
  exact (LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃
    (1 + Nat.card σ + 1) hK hF

/-- Finite projective dimension holds for all finitely presented modules over
a finite-variable polynomial ring over an arbitrary valuation domain. -/
theorem finiteProjectiveDimensionForFinitelyPresentedModules_mvPolynomial_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (σ : Type v) [Finite σ] :
    FiniteProjectiveDimensionForFinitelyPresentedModules (MvPolynomial σ R) := by
  intro M _ _ _
  exact ⟨1 + Nat.card σ + 1,
    hasProjectiveDimensionLE_of_finitePresentation_mvPolynomial_of_valuationRing M⟩

/-- Finite-variable polynomial rings over arbitrary valuation domains are coherent
and every finitely presented module over them has finite projective dimension. -/
theorem finitelyPresentedRegularRing_mvPolynomial_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (σ : Type v) [Finite σ] :
    FinitelyPresentedRegularRing (MvPolynomial σ R) :=
  ⟨finiteFreeSubmoduleCoherent_mvPolynomial_of_valuationRing,
    finiteProjectiveDimensionForFinitelyPresentedModules_mvPolynomial_of_valuationRing R σ⟩

/-- Every localization of such a polynomial ring has the same two properties. -/
theorem finitelyPresentedRegularRing_mvPolynomial_localization_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (σ : Type v) [Finite σ] (S : Submonoid (MvPolynomial σ R)) :
    FinitelyPresentedRegularRing (Localization S) :=
  finitelyPresentedRegularRing_localization
    (finitelyPresentedRegularRing_mvPolynomial_of_valuationRing R σ) S

end Langlands.CommutativeAlgebra
