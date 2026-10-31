import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentDiagram
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # The relative four-variable Laurent overlap comparison -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (f : A)

/-- The product-numerator tuple, with its fixed four-variable ordering. -/
def productNumerators : Fin 4 → A := ![f, 1, f ^ 2, f]

/-- The actual relative rational quotient for the product-numerator overlap. -/
abbrev ProductOverlap :=
  RelativeRationalPresentation.Algebra K A (PositivePolyradius.unit (Fin 4)) f
    (productNumerators K A f)

/-- The actual coefficient map of the four-variable quotient. -/
abbrev productBase : BoundedAlgHom K A (ProductOverlap K A f) :=
  RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 4)) f
    (productNumerators K A f)

/-- The actual fraction coordinate `Z_j` of the four-variable quotient. -/
abbrev productZ (j : Fin 4) : ProductOverlap K A f :=
  RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 4)) f
    (productNumerators K A f) j

theorem norm_productBase_le (a : A) : ‖productBase K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K A _ _ _ a

theorem norm_productZ_le (j : Fin 4) : ‖productZ K A f j‖ ≤ 1 :=
  RelativeRationalPresentation.norm_fraction_le K A _ _ _ j

/-- The unit bound also holds when the quotient is zero. -/
theorem norm_one_productOverlap_le : ‖(1 : ProductOverlap K A f)‖ ≤ 1 := by
  have h := norm_productBase_le K A f 1
  rw [show productBase K A f 1 = 1 from (productBase K A f).toAlgHom.map_one] at h
  exact h.trans (PresentedAffinoidAlgebra.norm_one_le K A)

/-- The four rational relations in the actual quotient. -/
theorem productBase_mul_productZ (j : Fin 4) :
    productBase K A f f * productZ K A f j =
      productBase K A f (productNumerators K A f j) :=
  RelativeRationalPresentation.fraction_equation K A _ _ _ j

/-- The second fraction is an inverse of the denominator image. -/
theorem productBase_mul_productZ_one :
    productBase K A f f * productZ K A f 1 = 1 := by
  have h := productBase_mul_productZ K A f 1
  change productBase K A f f * productZ K A f 1 = productBase K A f 1 at h
  exact h.trans (productBase K A f).toAlgHom.map_one

/-- Cancellation uses the displayed inverse, with no nonzero-ring premise. -/
private theorem productBase_mul_cancel {x y : ProductOverlap K A f}
    (h : productBase K A f f * x = productBase K A f f * y) : x = y := by
  calc
    x = (productBase K A f f * productZ K A f 1) * x := by
      rw [productBase_mul_productZ_one, one_mul]
    _ = productZ K A f 1 * (productBase K A f f * x) := by ac_rfl
    _ = productZ K A f 1 * (productBase K A f f * y) := by rw [h]
    _ = (productBase K A f f * productZ K A f 1) * y := by ac_rfl
    _ = y := by rw [productBase_mul_productZ_one, one_mul]

@[simp] theorem productZ_zero : productZ K A f 0 = 1 := by
  apply productBase_mul_cancel K A f
  rw [mul_one]
  have h := productBase_mul_productZ K A f 0
  change productBase K A f f * productZ K A f 0 = productBase K A f f at h
  exact h

@[simp] theorem productZ_two : productZ K A f 2 = productBase K A f f := by
  apply productBase_mul_cancel K A f
  have h := productBase_mul_productZ K A f 2
  change productBase K A f f * productZ K A f 2 = (productBase K A f).toAlgHom (f ^ 2) at h
  rw [map_pow, pow_two] at h
  exact h

@[simp] theorem productZ_three : productZ K A f 3 = 1 := by
  apply productBase_mul_cancel K A f
  rw [mul_one]
  have h := productBase_mul_productZ K A f 3
  change productBase K A f f * productZ K A f 3 = productBase K A f f at h
  exact h

/-- The forward substitution `(Z0,Z1,Z2,Z3) ↦ (1,Y,X,1)`. -/
def productForwardTuple : Fin 4 → Overlap K A f :=
  ![1, overlapY K A f, overlapX K A f, 1]

theorem norm_productForwardTuple_le (j : Fin 4) :
    ‖productForwardTuple K A f j‖ ≤ (PositivePolyradius.unit (Fin 4)) j := by
  fin_cases j
  · exact norm_one_overlap_le K A f
  · exact norm_overlapY_le K A f
  · exact norm_overlapX_le K A f
  · exact norm_one_overlap_le K A f

/-- The bound includes the empty monomial, using the quotient-unit bound. -/
theorem productForwardTuple_monomial_bound (d : Fin 4 →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue (Fin 4) (Overlap K A f)
      (productForwardTuple K A f) d‖ ≤ (PositivePolyradius.unit (Fin 4)).weight d :=
  monomialValue_norm_le_weight _ _ (norm_one_overlap_le K A f)
    (productForwardTuple K A f) (norm_productForwardTuple_le K A f) d

/-- The forward substitution satisfies all four rational relations. -/
theorem productForwardTuple_relations (j : Fin 4) :
    overlapBase K A f f * productForwardTuple K A f j =
      overlapBase K A f (productNumerators K A f j) := by
  fin_cases j
  · simp [productForwardTuple, productNumerators]
  · simpa [productForwardTuple, productNumerators] using overlapBase_mul_overlapY K A f
  · simp [productForwardTuple, productNumerators, overlapX_eq, pow_two]
  · simp [productForwardTuple, productNumerators]

/-- The reverse substitution `(X,Y) ↦ (Z2,Z1)`. -/
def productReverseTuple : Fin 2 → ProductOverlap K A f :=
  ![productZ K A f 2, productZ K A f 1]

theorem norm_productReverseTuple_le (j : Fin 2) :
    ‖productReverseTuple K A f j‖ ≤ (PositivePolyradius.unit (Fin 2)) j := by
  fin_cases j
  · exact norm_productZ_le K A f 2
  · exact norm_productZ_le K A f 1

theorem productReverseTuple_monomial_bound (d : Fin 2 →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue (Fin 2) (ProductOverlap K A f)
      (productReverseTuple K A f) d‖ ≤ (PositivePolyradius.unit (Fin 2)).weight d :=
  monomialValue_norm_le_weight _ _ (norm_one_productOverlap_le K A f)
    (productReverseTuple K A f) (norm_productReverseTuple_le K A f) d

section Maps

variable [CompleteSpace K]

/-- Convergent relative coefficient evaluation, descended through the four
closed rational relations. -/
def productToOverlap : BoundedAlgHom K (ProductOverlap K A f) (Overlap K A f) :=
  RelativeRationalPresentation.evaluate K A (PositivePolyradius.unit (Fin 4)) f
    (productNumerators K A f) (Overlap K A f) (overlapBase K A f)
    (productForwardTuple K A f) (norm_overlapBase_le K A f)
    (productForwardTuple_monomial_bound K A f) (productForwardTuple_relations K A f)

@[simp] theorem productToOverlap_baseMap (a : A) :
    productToOverlap K A f (productBase K A f a) = overlapBase K A f a :=
  RelativeRationalPresentation.evaluate_baseMap K A _ _ _ _ _ _ _ _ _ a

@[simp] theorem productToOverlap_fraction (j : Fin 4) :
    productToOverlap K A f (productZ K A f j) = productForwardTuple K A f j :=
  RelativeRationalPresentation.evaluate_fraction K A _ _ _ _ _ _ _ _ _ j

theorem norm_productToOverlap_le (a : ProductOverlap K A f) :
    ‖productToOverlap K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le K A _ _ _ _ _ _ _ _ _ a

/-- The constructed relative-series evaluation for the reverse substitution. -/
def productInverseEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A)
      (ProductOverlap K A f) :=
  evaluateCoefficientsHom (PositivePolyradius.unit (Fin 2)) (productBase K A f)
    (productReverseTuple K A f) (norm_productBase_le K A f)
    (productReverseTuple_monomial_bound K A f)

/-- Reverse evaluation annihilates each of the two overlap equations. -/
theorem productInverseEvaluation_equations :
    ∀ h ∈ overlapEquations K A f, productInverseEvaluation K A f h = 0 := by
  intro h hh
  rcases hh with rfl | hh
  · change (productInverseEvaluation K A f).toAlgHom
      (X (PositivePolyradius.unit (Fin 2)) A 0 -
        constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f) = 0
    rw [map_sub]
    change evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
      (X _ A 0) - evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
        (constantAlgHom _ K A f) = 0
    rw [evaluateCoefficients_X, evaluateCoefficients_constant]
    simp [productReverseTuple]
  · have heq := Set.mem_singleton_iff.mp hh
    subst h
    change (productInverseEvaluation K A f).toAlgHom
      (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f *
        X (PositivePolyradius.unit (Fin 2)) A 1 - 1) = 0
    rw [map_sub, map_mul, map_one]
    change evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
      (constantAlgHom _ K A f) *
      evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
        (X _ A 1) - 1 = 0
    rw [evaluateCoefficients_constant, evaluateCoefficients_X]
    simpa [productReverseTuple] using sub_eq_zero.mpr (productBase_mul_productZ_one K A f)

/-- The reverse bounded map, by closed-ideal descent of convergent evaluation. -/
def overlapToProduct : BoundedAlgHom K (Overlap K A f) (ProductOverlap K A f) :=
  RelativeRelations.descend K A (PositivePolyradius.unit (Fin 2)) (overlapEquations K A f)
    (ProductOverlap K A f) (productInverseEvaluation K A f)
    (productInverseEvaluation_equations K A f)

@[simp] theorem overlapToProduct_baseMap (a : A) :
    overlapToProduct K A f (overlapBase K A f a) = productBase K A f a := by
  change evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
    (constantAlgHom _ K A a) = _
  exact evaluateCoefficients_constant _ _ _ a

@[simp] theorem overlapToProduct_overlapX :
    overlapToProduct K A f (overlapX K A f) = productZ K A f 2 := by
  change evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
    (X _ A 0) = _
  exact evaluateCoefficients_X _ _ _ 0

@[simp] theorem overlapToProduct_overlapY :
    overlapToProduct K A f (overlapY K A f) = productZ K A f 1 := by
  change evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f)
    (X _ A 1) = _
  exact evaluateCoefficients_X _ _ _ 1

theorem norm_overlapToProduct_le (a : Overlap K A f) :
    ‖overlapToProduct K A f a‖ ≤ ‖a‖ := by
  have h := RelativeRelations.norm_descend_le K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f) (ProductOverlap K A f) (productInverseEvaluation K A f)
    (productInverseEvaluation_equations K A f) 1 zero_lt_one
    (fun h => by
      change ‖evaluateCoefficients _ (productBase K A f) (productReverseTuple K A f) h‖ ≤
        1 * ‖h‖
      simpa only [one_mul] using norm_evaluateCoefficients_le _ (productBase K A f)
        (productReverseTuple K A f) (norm_productBase_le K A f)
        (productReverseTuple_monomial_bound K A f) h) a
  simpa only [overlapToProduct, one_mul] using h

/-- The product composite is the identity, proved on coefficients and all fractions. -/
theorem overlapToProduct_comp_productToOverlap :
    (overlapToProduct K A f).comp (productToOverlap K A f) =
      BoundedAlgHom.id K (ProductOverlap K A f) := by
  apply RelativeRationalPresentation.hom_ext K A (PositivePolyradius.unit (Fin 4)) f
    (productNumerators K A f) (ProductOverlap K A f)
  · intro a
    change overlapToProduct K A f (productToOverlap K A f (productBase K A f a)) =
      productBase K A f a
    rw [productToOverlap_baseMap, overlapToProduct_baseMap]
  · intro j
    change overlapToProduct K A f (productToOverlap K A f (productZ K A f j)) =
      productZ K A f j
    rw [productToOverlap_fraction]
    fin_cases j
    · change (overlapToProduct K A f).toAlgHom 1 = productZ K A f 0
      simp
    · change overlapToProduct K A f (overlapY K A f) = productZ K A f 1
      exact overlapToProduct_overlapY K A f
    · change overlapToProduct K A f (overlapX K A f) = productZ K A f 2
      exact overlapToProduct_overlapX K A f
    · change (overlapToProduct K A f).toAlgHom 1 = productZ K A f 3
      simp

/-- The overlap composite is the identity, proved on coefficients, `X` and `Y`. -/
theorem productToOverlap_comp_overlapToProduct :
    (productToOverlap K A f).comp (overlapToProduct K A f) =
      BoundedAlgHom.id K (Overlap K A f) := by
  apply overlap_hom_ext K A f
  · intro a
    change productToOverlap K A f (overlapToProduct K A f (overlapBase K A f a)) =
      overlapBase K A f a
    rw [overlapToProduct_baseMap, productToOverlap_baseMap]
  · change productToOverlap K A f (overlapToProduct K A f (overlapX K A f)) =
      overlapX K A f
    rw [overlapToProduct_overlapX, productToOverlap_fraction]
    rfl
  · change productToOverlap K A f (overlapToProduct K A f (overlapY K A f)) =
      overlapY K A f
    rw [overlapToProduct_overlapY, productToOverlap_fraction]
    rfl

/-- The actual four-variable to two-variable bounded Laurent overlap equivalence. -/
def productOverlapEquiv : BoundedAlgEquiv K (ProductOverlap K A f) (Overlap K A f) :=
  BoundedAlgEquiv.ofHomInv (productToOverlap K A f) (overlapToProduct K A f)
    (fun a => congrArg (fun φ : BoundedAlgHom K (ProductOverlap K A f)
      (ProductOverlap K A f) => φ a) (overlapToProduct_comp_productToOverlap K A f))
    (fun a => congrArg (fun φ : BoundedAlgHom K (Overlap K A f)
      (Overlap K A f) => φ a) (productToOverlap_comp_overlapToProduct K A f))

@[simp] theorem productOverlapEquiv_baseMap (a : A) :
    productOverlapEquiv K A f
      (RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 4)) f
        (productNumerators K A f) a) = overlapBase K A f a :=
  productToOverlap_baseMap K A f a

/-- All four forward coordinate laws in the specified order. -/
@[simp] theorem productOverlapEquiv_fraction (j : Fin 4) :
    productOverlapEquiv K A f
      (RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 4)) f
        (productNumerators K A f) j) = ![1, overlapY K A f, overlapX K A f, 1] j :=
  productToOverlap_fraction K A f j

@[simp] theorem productOverlapEquiv_symm_baseMap (a : A) :
    (productOverlapEquiv K A f).symm (overlapBase K A f a) =
      RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 4)) f
        (productNumerators K A f) a :=
  overlapToProduct_baseMap K A f a

@[simp] theorem productOverlapEquiv_symm_overlapX :
    (productOverlapEquiv K A f).symm (overlapX K A f) =
      RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 4)) f
        (productNumerators K A f) 2 :=
  overlapToProduct_overlapX K A f

@[simp] theorem productOverlapEquiv_symm_overlapY :
    (productOverlapEquiv K A f).symm (overlapY K A f) =
      RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 4)) f
        (productNumerators K A f) 1 :=
  overlapToProduct_overlapY K A f

end Maps

end Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent
