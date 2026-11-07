import Langlands.GroupScheme.MatrixRepresentation.FrobeniusHopfAlgebra
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusTopIntegral
import Langlands.Algebra.NormalizedHopfIntegral
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # A perfect convolution pairing on the actual Frobenius quotient dual -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionPairing

open FrobeniusCoordinateModel FrobeniusPolynomialBox FrobeniusDistributionAlgebra
open FrobeniusConvolutionAction FrobeniusTopIntegral FrobeniusHopfAlgebra
open TorusUnipotence CoordinateWeights
open Langlands.Algebra.PolynomialBoxQuotient

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local notation "Q" => quotientAlgebra G p r
local notation "D" => DistributionAlgebra (G := G) p r

/-- Convolution followed by evaluation at a genuine quotient coordinate. -/
def convolutionForm (q : Q) : LinearMap.BilinForm k D :=
  (LinearMap.mul k D).compr₂
    (((Module.Dual.eval k Q) q).comp (WithConv.linearEquiv k _).toLinearMap)

@[simp]
theorem convolutionForm_apply (q : Q) (f g : D) :
    convolutionForm p r q f g = (f * g).ofConv q := rfl

/-- Multiplication by the top box monomial retains precisely the constant coefficient. -/
theorem box_mul_top {σ : Type*} (N : σ →₀ ℕ)
    (x : boxAlgebra (k := k) N) :
    x * Ideal.Quotient.mkₐ k (boxIdeal N) (monomial N (1 : k)) =
      coefficient N 0 (zero_le : (0 : σ →₀ ℕ) ≤ N) x •
        Ideal.Quotient.mkₐ k (boxIdeal N) (monomial N (1 : k)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (boxIdeal N) x
  apply coefficients_injective N
  ext a
  rw [← map_mul, map_smul]
  change (P * monomial N (1 : k)).coeff a.val =
    P.coeff 0 * (monomial N (1 : k)).coeff a.val
  rw [coeff_mul_monomial', coeff_monomial]
  by_cases h : N ≤ a.val
  · have he : N = a.val := le_antisymm h a.property
    simp [he]
  · have he : N ≠ a.val := fun he => h (le_of_eq he)
    simp [h, he]

variable {d : ℕ} (t : Fin d → CharacterUnits.Coord G)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G))
    (hε : ∀ i, coordCounit G (t i) = 0)

local notation "N" => bound p d r

/-- The class of the top retained monomial in the actual coordinate quotient. -/
def topCoordinate : Q :=
  quotientMap G p r ((polynomialCoordinates t ht).symm (monomial N (1 : k)))

/-- The coordinate and dual integrals have pairing exactly one. -/
theorem topDistribution_topCoordinate :
    (topDistribution p r t ht hε).ofConv (topCoordinate p r t ht) = 1 := by
  rw [topCoordinate, topDistribution_quotientMap, AlgEquiv.apply_symm_apply,
    coeff_monomial, ite_eq_left rfl]

include hε in
/-- The top coordinate is an integral for ordinary coordinate multiplication. -/
theorem mul_topCoordinate (a : Q) :
    a * topCoordinate p r t ht =
      Coalgebra.counit (R := k) a • topCoordinate p r t ht := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (quotientIdeal G p r) a
  let e := polynomialModelEquiv G p r (polynomialCoordinates t ht)
    (polynomialCoordinates_origin t ht hε)
  apply e.injective
  rw [map_mul, map_smul]
  change Ideal.Quotient.mkₐ k (boxIdeal N) (polynomialCoordinates t ht f) *
      Ideal.Quotient.mkₐ k (boxIdeal N)
        ((polynomialCoordinates t ht)
          ((polynomialCoordinates t ht).symm (monomial N (1 : k)))) =
    Lie.coordinateOrigin G f • Ideal.Quotient.mkₐ k (boxIdeal N)
      ((polynomialCoordinates t ht)
        ((polynomialCoordinates t ht).symm (monomial N (1 : k))))
  rw [AlgEquiv.apply_symm_apply, box_mul_top, coefficient_mk,
    polynomialCoordinates_origin t ht hε]

variable {S : CommGroupScheme (Spec (.of k))}
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (ν : cocharacterLattice S) (w : Fin d → characterLattice S)
    (htw : ∀ i, t i ∈ CoordinateWeights.weightSpace b (w i))
    (hw : ∀ i, 0 < latticePairing S (w i) ν)

include hε hS htw hw in
/-- Actual convolution evaluation at the top coordinate has no left radical. -/
theorem convolutionForm_separatingLeft :
    (convolutionForm p r (topCoordinate p r t ht)).SeparatingLeft := by
  intro f hf
  exact Langlands.NormalizedHopfIntegral.eq_zero_of_forall_conv_eval_eq_zero
    (topCoordinate p r t ht) (topDistribution p r t ht hε).ofConv
    (mul_topCoordinate p r t ht hε)
    (by
      intro ell
      simpa only [WithConv.toConv_ofConv] using
        mul_top p r hS b ν w t ht htw hε hw ell)
    (topDistribution_topCoordinate p r t ht hε)
    (antipode_involutive G p r) f hf

include hε hS htw hw in
/-- The actual full convolution algebra has a perfect evaluation pairing. -/
theorem convolutionForm_nondegenerate :
    (convolutionForm p r (topCoordinate p r t ht)).Nondegenerate := by
  let : Module.Finite k Q := finite_quotientAlgebra G p r
    (polynomialCoordinates t ht) (polynomialCoordinates_origin t ht hε)
  let : Module.Finite k D := Module.Finite.equiv (WithConv.linearEquiv k _).symm
  exact LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (convolutionForm_separatingLeft p r t ht hε hS b ν w htw hw)

include hS in
/-- Smoothness and positive augmentation weights supply a perfect convolution pairing. -/
theorem exists_nondegenerate_convolutionForm
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (hsupp : ∀ χ ∈ CoordinateWeights.support b, 0 < latticePairing S χ ν) :
    ∃ q : Q, (convolutionForm p r q).Nondegenerate := by
  obtain ⟨d, w, t, ht, htw, hε, hw, -⟩ := exists_positiveWeight_coordinates hS b ν hsupp
  exact ⟨topCoordinate p r t ht,
    convolutionForm_nondegenerate p r t ht hε hS b ν w htw hw⟩

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionPairing
