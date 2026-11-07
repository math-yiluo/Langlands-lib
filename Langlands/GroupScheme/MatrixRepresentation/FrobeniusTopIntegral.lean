import Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionAction
import Langlands.GroupScheme.Rational.TorusUnipotence.PositiveWeightCoordinates

/-! # Top integrals of actual positively weighted Frobenius kernels -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial Finsupp
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusTopIntegral

open FrobeniusCoordinateModel FrobeniusPolynomialBox FrobeniusDistributionAlgebra
open FrobeniusConvolutionAction TorusUnipotence CoordinateWeights
open Langlands.Algebra.PolynomialBoxQuotient
open Langlands.Algebra.WeightGradedFormallySmooth

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)
    {S : CommGroupScheme (Spec (.of k))}
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (ν : cocharacterLattice S)
    {d : ℕ} (w : Fin d → characterLattice S) (t : Fin d → CharacterUnits.Coord G)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G))
    (htw : ∀ i, t i ∈ CoordinateWeights.weightSpace b (w i))
    (hε : ∀ i, coordCounit G (t i) = 0)
    (hw : ∀ i, 0 < latticePairing S (w i) ν)

local notation "C" => CharacterUnits.Coord G
local notation "Q" => quotientAlgebra G p r
local notation "N" => bound p d r

/-- The polynomial coordinates supplied by the actual eigenfunctions. -/
def polynomialCoordinates : C ≃ₐ[k] MvPolynomial (Fin d) k :=
  (AlgEquiv.ofBijective (aeval t) ht).symm

include hε in
theorem polynomialCoordinates_origin (f : C) :
    (polynomialCoordinates t ht f).coeff 0 = Lie.coordinateOrigin G f := by
  have he : (Lie.coordinateOrigin G).comp (aeval t) =
      (aeval (0 : Fin d → k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    exact hε i
  have h := AlgHom.congr_fun he (polynomialCoordinates t ht f)
  change Lie.coordinateOrigin G
    ((AlgEquiv.ofBijective (aeval t) ht) ((AlgEquiv.ofBijective (aeval t) ht).symm f)) =
      aeval (0 : Fin d → k) (polynomialCoordinates t ht f) at h
  rw [AlgEquiv.apply_symm_apply] at h
  simpa only [aeval_zero, constantCoeff_eq,
    Algebra.algebraMap_self_apply] using h.symm

/-- All retained monomial coordinates of the actual quotient, as a basis. -/
def quotientBasis : Module.Basis (Set.Iic N) k Q :=
  Module.Basis.ofEquivFun
    ((polynomialModelEquiv G p r (polynomialCoordinates t ht)
      (polynomialCoordinates_origin t ht hε)).toLinearEquiv.trans
        (coefficientsEquiv N))

theorem quotientBasis_repr (f : C) (a : Set.Iic N) :
    (quotientBasis p r t ht hε).repr (quotientMap G p r f) a =
      (polynomialCoordinates t ht f).coeff a.val := rfl

theorem quotientBasis_apply (a : Set.Iic N) :
    quotientBasis p r t ht hε a =
      quotientMap G p r ((polynomialCoordinates t ht).symm (monomial a.val (1 : k))) := by
  classical
  apply (quotientBasis p r t ht hε).repr.injective
  ext a'
  rw [Module.Basis.repr_self, quotientBasis_repr,
    AlgEquiv.apply_symm_apply, coeff_monomial]
  simp only [Finsupp.single_apply]
  by_cases h : a = a'
  · subst a'
    simp
  · have h' : a.val ≠ a'.val := fun h' => h (Subtype.ext h')
    simp [h, h']

/-- The top retained coefficient, as an element of the genuine convolution dual. -/
def topDistribution : DistributionAlgebra (G := G) p r :=
  WithConv.toConv ((coefficient N N le_rfl).comp
    (polynomialModelEquiv G p r (polynomialCoordinates t ht)
      (polynomialCoordinates_origin t ht hε)).toLinearEquiv.toLinearMap)

@[simp]
theorem topDistribution_quotientMap (f : C) :
    (topDistribution p r t ht hε).ofConv (quotientMap G p r f) =
      (polynomialCoordinates t ht f).coeff N := rfl

theorem topDistribution_ne_zero :
    topDistribution p r t ht hε ≠ 0 := by
  intro h
  have hh := congrArg
    (fun ell : DistributionAlgebra (G := G) p r =>
      ell.ofConv (quotientMap G p r
        ((polynomialCoordinates t ht).symm (monomial N (1 : k))))) h
  rw [topDistribution_quotientMap, AlgEquiv.apply_symm_apply, coeff_monomial,
    ite_eq_left rfl] at hh
  exact one_ne_zero hh

include hS htw in
theorem polynomialCoordinates_homogeneous {χ : characterLattice S}
    {f : C} (hf : f ∈ CoordinateWeights.weightSpace b χ) :
    IsWeightedHomogeneous w (polynomialCoordinates t ht f) χ := by
  classical
  let _ := weightGradedAlgebra hS b
  apply isWeightedHomogeneous_of_aeval_mem (CoordinateWeights.weightSpace b) htw ht.1
  change (AlgEquiv.ofBijective (aeval t) ht)
    ((AlgEquiv.ofBijective (aeval t) ht).symm f) ∈ _
  rwa [AlgEquiv.apply_symm_apply]

include hS htw in
theorem monomial_mem_weightSpace (a : Fin d →₀ ℕ) :
    (polynomialCoordinates t ht).symm (monomial a (1 : k)) ∈
      CoordinateWeights.weightSpace b (weight w a) := by
  let _ := weightGradedAlgebra hS b
  change aeval t (monomial a (1 : k)) ∈ _
  exact aeval_mem_graded_of_isWeightedHomogeneous (CoordinateWeights.weightSpace b) htw
    (isWeightedHomogeneous_monomial w a 1 rfl)

include hS htw in
theorem topDistribution_eq_zero_of_height_ne {χ : characterLattice S}
    {f : C} (hf : f ∈ CoordinateWeights.weightSpace b χ)
    (hχ : latticePairing S χ ν ≠ latticePairing S (weight w N) ν) :
    (topDistribution p r t ht hε).ofConv (quotientMap G p r f) = 0 := by
  rw [topDistribution_quotientMap]
  by_contra hf0
  have hh := polynomialCoordinates_homogeneous hS b w t ht htw hf hf0
  exact hχ (congrArg (fun ψ => latticePairing S ψ ν) hh.symm)

include hS htw hε hw ht in
theorem nonpositive_weight_eq_scalar {χ : characterLattice S}
    {f : C} (hf : f ∈ CoordinateWeights.weightSpace b χ)
    (hχ : latticePairing S χ ν ≤ 0) :
    f = algebraMap k C (Lie.coordinateOrigin G f) := by
  apply (polynomialCoordinates t ht).injective
  rw [AlgEquiv.commutes]
  apply MvPolynomial.ext
  intro a
  change _ = (MvPolynomial.C (Lie.coordinateOrigin G f) : MvPolynomial (Fin d) k).coeff a
  by_cases ha : a = 0
  · subst a
    rw [polynomialCoordinates_origin t ht hε, coeff_C, ite_eq_left rfl]
  · rw [coeff_C, ite_eq_right (Ne.symm ha)]
    by_contra hc
    have hh := polynomialCoordinates_homogeneous hS b w t ht htw hf hc
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (Finsupp.ext h)
    let height : characterLattice S →+ ℤ :=
      ((latticePairing S).flip ν).toAddMonoidHom
    have hle := le_weight_of_ne_zero (w := fun j => height (w j))
      (fun j => (hw j).le) hi
    rw [← height_weight height w a, hh] at hle
    exact (not_lt_of_ge hχ) ((hw i).trans_le hle)

include hS htw hε hw ht in
theorem distribution_eq_zero_on_nonpositive
    (ell : DistributionAlgebra (G := G) p r) (hell : ell.ofConv 1 = 0)
    {χ : characterLattice S} {f : C} (hf : f ∈ CoordinateWeights.weightSpace b χ)
    (hχ : latticePairing S χ ν ≤ 0) :
    ell.ofConv (quotientMap G p r f) = 0 := by
  rw [nonpositive_weight_eq_scalar hS b ν w t ht htw hε hw hf hχ,
    AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, hell, smul_zero]

/-- Contract both factors of the genuine coordinate coproduct after quotienting. -/
def coordinateContraction
    (ell1 ell2 : DistributionAlgebra (G := G) p r) : C ⊗[k] C →ₗ[k] k :=
  (LinearMap.mul' k k).comp
    ((TensorProduct.map ell1.ofConv ell2.ofConv).comp
      (TensorProduct.map (quotientMap G p r).toLinearMap (quotientMap G p r).toLinearMap))

theorem coordinateContraction_tmul
    (ell1 ell2 : DistributionAlgebra (G := G) p r) (f g : C) :
    coordinateContraction p r ell1 ell2 (f ⊗ₜ[k] g) =
      ell1.ofConv (quotientMap G p r f) * ell2.ofConv (quotientMap G p r g) := by
  simp [coordinateContraction]

theorem convMul_quotientMap
    (ell1 ell2 : DistributionAlgebra (G := G) p r) (f : C) :
    (ell1 * ell2).ofConv (quotientMap G p r f) =
      coordinateContraction p r ell1 ell2 (coordComul G f) := by
  rw [LinearMap.convMul_apply, comul_quotientMap]
  rfl

include hS htw hw in
theorem convolution_eq_zero_on_homogeneous
    (ell : DistributionAlgebra (G := G) p r) (hell : ell.ofConv 1 = 0)
    {χ : characterLattice S} {f : C} (hf : f ∈ CoordinateWeights.weightSpace b χ)
    (hχ : latticePairing S χ ν ≤ latticePairing S (weight w N) ν) :
    (topDistribution p r t ht hε * ell).ofConv (quotientMap G p r f) = 0 ∧
      (ell * topDistribution p r t ht hε).ofConv (quotientMap G p r f) = 0 := by
  let height : characterLattice S →+ ℤ :=
    ((latticePairing S).flip ν).toAddMonoidHom
  have hleft : (⨆ α, Submodule.map₂ (TensorProduct.mk k C C)
      (CoordinateWeights.weightSpace b α) (CoordinateWeights.weightSpace b (χ - α))) ≤
      LinearMap.ker (coordinateContraction p r (topDistribution p r t ht hε) ell) := by
    refine iSup_le fun α => Submodule.map₂_le.2 fun a ha a' ha' => ?_
    change coordinateContraction p r (topDistribution p r t ht hε) ell (a ⊗ₜ[k] a') = 0
    rw [coordinateContraction_tmul]
    by_cases hα : height α = height (weight w N)
    · have hβ : height (χ - α) ≤ 0 := by
        rw [map_sub]
        change height χ ≤ height (weight w N) at hχ
        omega
      rw [distribution_eq_zero_on_nonpositive p r hS b ν w t ht htw hε hw ell hell ha' hβ,
        mul_zero]
    · rw [topDistribution_eq_zero_of_height_ne p r hS b ν w t ht htw hε ha hα, zero_mul]
  have hright : (⨆ α, Submodule.map₂ (TensorProduct.mk k C C)
      (CoordinateWeights.weightSpace b α) (CoordinateWeights.weightSpace b (χ - α))) ≤
      LinearMap.ker (coordinateContraction p r ell (topDistribution p r t ht hε)) := by
    refine iSup_le fun α => Submodule.map₂_le.2 fun a ha a' ha' => ?_
    change coordinateContraction p r ell (topDistribution p r t ht hε) (a ⊗ₜ[k] a') = 0
    rw [coordinateContraction_tmul]
    by_cases hβ : height (χ - α) = height (weight w N)
    · have hα : height α ≤ 0 := by
        rw [map_sub] at hβ
        change height χ ≤ height (weight w N) at hχ
        omega
      rw [distribution_eq_zero_on_nonpositive p r hS b ν w t ht htw hε hw ell hell ha hα,
        zero_mul]
    · rw [topDistribution_eq_zero_of_height_ne p r hS b ν w t ht htw hε ha' hβ, mul_zero]
  rw [convMul_quotientMap, convMul_quotientMap]
  exact ⟨hleft (coordComul_mem_iSup b hS hf), hright (coordComul_mem_iSup b hS hf)⟩

include hw in
omit [ExpChar k p] in
theorem box_height_le (a : Set.Iic N) :
    latticePairing S (weight w a.val) ν ≤ latticePairing S (weight w N) ν := by
  let height : characterLattice S →+ ℤ :=
    ((latticePairing S).flip ν).toAddMonoidHom
  change height (weight w a.val) ≤ height (weight w N)
  rw [height_weight, height_weight, weight_eq_sum, weight_eq_sum]
  exact Finset.sum_le_sum fun i _ => nsmul_le_nsmul_left (hw i).le (a.property i)

include hS htw hw in
theorem top_mul_eq_zero_of_one_eq_zero
    (ell : DistributionAlgebra (G := G) p r) (hell : ell.ofConv 1 = 0) :
    topDistribution p r t ht hε * ell = 0 := by
  apply WithConv.ofConv_injective
  apply (quotientBasis p r t ht hε).ext
  intro a
  rw [quotientBasis_apply]
  exact (convolution_eq_zero_on_homogeneous p r hS b ν w t ht htw hε hw ell hell
    (monomial_mem_weightSpace hS b w t ht htw a.val)
    (box_height_le p r ν w hw a)).1

include hS htw hw in
theorem mul_top_eq_zero_of_one_eq_zero
    (ell : DistributionAlgebra (G := G) p r) (hell : ell.ofConv 1 = 0) :
    ell * topDistribution p r t ht hε = 0 := by
  apply WithConv.ofConv_injective
  apply (quotientBasis p r t ht hε).ext
  intro a
  rw [quotientBasis_apply]
  exact (convolution_eq_zero_on_homogeneous p r hS b ν w t ht htw hε hw ell hell
    (monomial_mem_weightSpace hS b w t ht htw a.val)
    (box_height_le p r ν w hw a)).2

include hS htw hw in
theorem top_mul (ell : DistributionAlgebra (G := G) p r) :
    topDistribution p r t ht hε * ell =
      ell.ofConv 1 • topDistribution p r t ht hε := by
  have hunit : (1 : DistributionAlgebra (G := G) p r).ofConv 1 = 1 := by
    change Bialgebra.counitAlgHom k Q 1 = 1
    exact map_one _
  have hell : (ell - ell.ofConv 1 • (1 : DistributionAlgebra (G := G) p r)).ofConv 1 = 0 := by
    change ell.ofConv 1 - ell.ofConv 1 • (1 : DistributionAlgebra (G := G) p r).ofConv 1 = 0
    rw [hunit, smul_eq_mul, mul_one, sub_self]
  have h := top_mul_eq_zero_of_one_eq_zero p r hS b ν w t ht htw hε hw _ hell
  rw [mul_sub, mul_smul_comm, mul_one] at h
  exact sub_eq_zero.mp h

include hS htw hw in
theorem mul_top (ell : DistributionAlgebra (G := G) p r) :
    ell * topDistribution p r t ht hε =
      ell.ofConv 1 • topDistribution p r t ht hε := by
  have hunit : (1 : DistributionAlgebra (G := G) p r).ofConv 1 = 1 := by
    change Bialgebra.counitAlgHom k Q 1 = 1
    exact map_one _
  have hell : (ell - ell.ofConv 1 • (1 : DistributionAlgebra (G := G) p r)).ofConv 1 = 0 := by
    change ell.ofConv 1 - ell.ofConv 1 • (1 : DistributionAlgebra (G := G) p r).ofConv 1 = 0
    rw [hunit, smul_eq_mul, mul_one, sub_self]
  have h := mul_top_eq_zero_of_one_eq_zero p r hS b ν w t ht htw hε hw _ hell
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  exact sub_eq_zero.mp h

include hS in
/-- Positive augmentation weights give an actual nonzero two-sided convolution integral. -/
theorem exists_nonzero_twoSidedIntegral
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (hsupp : ∀ χ ∈ CoordinateWeights.support b, 0 < latticePairing S χ ν) :
    ∃ z : DistributionAlgebra (G := G) p r, z ≠ 0 ∧
      ∀ ell : DistributionAlgebra (G := G) p r,
        z * ell = ell.ofConv 1 • z ∧ ell * z = ell.ofConv 1 • z := by
  obtain ⟨d, w, t, ht, htw, hε, hw, -⟩ := exists_positiveWeight_coordinates hS b ν hsupp
  exact ⟨topDistribution p r t ht hε, topDistribution_ne_zero p r t ht hε,
    fun ell => ⟨top_mul p r hS b ν w t ht htw hε hw ell,
      mul_top p r hS b ν w t ht htw hε hw ell⟩⟩

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusTopIntegral
