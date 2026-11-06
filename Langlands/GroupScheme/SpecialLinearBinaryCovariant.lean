import Langlands.GroupScheme.SpecialLinearBinaryCharts
import Mathlib.RingTheory.Localization.FractionRing

/-! # Exhaustion of binary upper-covariant coordinates by homogeneous polynomials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

variable {k : Type u} [Field k]

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance : IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

local instance : IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance : IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

/-- The two entries in the bottom row of the universal matrix generate the unit ideal. -/
theorem bottomRow_span :
    Ideal.span {universal (Fin 2) k 1 0, universal (Fin 2) k 1 1} = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := (universal (Fin 2) k).property
  rw [Matrix.det_fin_two] at h
  have hm : universal (Fin 2) k 0 0 * universal (Fin 2) k 1 1 -
      universal (Fin 2) k 0 1 * universal (Fin 2) k 1 0 ∈
      Ideal.span {universal (Fin 2) k 1 0, universal (Fin 2) k 1 1} :=
    Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  simpa only [h] using hm

/-- Vanishing of the two restrictions forces a covariant coordinate to vanish. -/
theorem eq_zero_of_restrictions (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    (hP : lowerRestriction F = 0) (hQ : otherRestriction F = 0) : F = 0 := by
  let c := universal (Fin 2) k 1 0
  let d := universal (Fin 2) k 1 1
  have hc : algebraMap (CoordinateRing (Fin 2) k) (Localization.Away c) F = 0 := by
    let f := IsScalarTower.toAlgHom k (CoordinateRing (Fin 2) k) (Localization.Away c)
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    have e := classify_eq_otherRestriction m F hF (point f) v hv
    simpa [hQ, classify_point, f] using e
  have hd : algebraMap (CoordinateRing (Fin 2) k) (Localization.Away d) F = 0 := by
    let f := IsScalarTower.toAlgHom k (CoordinateRing (Fin 2) k) (Localization.Away d)
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d
    have e := classify_eq_lowerRestriction m F hF (point f) v hv
    simpa [hP, classify_point, f] using e
  apply Localization.algebraMap_injective_of_span_eq_top {c, d} bottomRow_span
  funext ⟨a, ha⟩
  change algebraMap (CoordinateRing (Fin 2) k) (Localization.Away a) F =
    algebraMap (CoordinateRing (Fin 2) k) (Localization.Away a) 0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · simpa only [map_zero] using hc
  · simpa only [map_zero] using hd

/-- A covariant coordinate satisfies the transition formula on the overlap over every algebra. -/
theorem restriction_overlap (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    {S : Type u} [CommRing S] [Algebra k S] (v : Sˣ) :
    Polynomial.aeval (v : S) (lowerRestriction F) =
      (v : S) ^ m * Polynomial.aeval (↑v⁻¹ : S) (otherRestriction F) := by
  have h := classify_eq_otherRestriction m F hF (lowerChart (v : S)) v rfl
  rw [classify_lowerChart] at h
  simpa [lowerChart] using h

/-- The transition equation is a polynomial identity, valid also over finite fields. -/
theorem restriction_reverse (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m)) :
    Polynomial.X ^ (otherRestriction F).natDegree * lowerRestriction F =
      Polynomial.X ^ m * (otherRestriction F).reverse := by
  let K := FractionRing (Polynomial k)
  let x : K := algebraMap (Polynomial k) K Polynomial.X
  have hx : x ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) K)).mpr Polynomial.X_ne_zero
  let v : Kˣ := Units.mk0 x hx
  have h : Polynomial.aeval x (lowerRestriction F) =
      x ^ m * Polynomial.aeval (x⁻¹) (otherRestriction F) := by
    simpa [v] using restriction_overlap m F hF v
  let : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap k K) (x⁻¹)
    (otherRestriction F)
  have heval (P : Polynomial k) : Polynomial.aeval x P = algebraMap (Polynomial k) K P := by
    have e : (Polynomial.aeval x : Polynomial k →ₐ[k] K) =
        IsScalarTower.toAlgHom k (Polynomial k) K := by
      apply Polynomial.algHom_ext
      simp [x]
    exact AlgHom.congr_fun e P
  apply IsFractionRing.injective (Polynomial k) K
  simp only [map_mul, map_pow, ← heval, Polynomial.aeval_X]
  rw [h]
  have hr : Polynomial.aeval x (otherRestriction F).reverse =
      x ^ (otherRestriction F).natDegree * Polynomial.aeval (x⁻¹) (otherRestriction F) := by
    have e : Polynomial.aeval x (otherRestriction F).reverse *
        (x ^ (otherRestriction F).natDegree)⁻¹ =
        Polynomial.aeval (x⁻¹) (otherRestriction F) := by
      have hi : (⅟(x⁻¹) : K) = x :=
        (invOf_eq_inv (x⁻¹)).trans (inv_inv x)
      simpa only [hi, inv_pow, Polynomial.aeval_def] using hrev
    have e' := (div_eq_iff (pow_ne_zero _ hx)).mp
      (show Polynomial.aeval x (otherRestriction F).reverse /
        x ^ (otherRestriction F).natDegree =
        Polynomial.aeval (x⁻¹) (otherRestriction F) from e)
    simpa only [mul_comm] using e'
  rw [hr]
  ring


/-- Regularity on both charts bounds the degree of the lower restriction by the weight. -/
theorem lowerRestriction_natDegree_le (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m)) :
    (lowerRestriction F).natDegree ≤ m := by
  by_cases hP : lowerRestriction F = 0
  · simp [hP]
  have h := congrArg Polynomial.natDegree (restriction_reverse m F hF)
  rw [Polynomial.natDegree_X_pow_mul _ hP] at h
  have hbound := Polynomial.natDegree_mul_le
    (p := (Polynomial.X : Polynomial k) ^ m) (q := (otherRestriction F).reverse)
  rw [Polynomial.natDegree_X_pow] at hbound
  have hrev := (otherRestriction F).reverse_natDegree_le
  omega

/-- A single chart determines the whole covariant coordinate. -/
theorem eq_zero_of_lowerRestriction (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    (hP : lowerRestriction F = 0) : F = 0 := by
  have h := restriction_reverse m F hF
  rw [hP, mul_zero] at h
  have hQ : otherRestriction F = 0 := by
    apply Polynomial.reverse_eq_zero.mp
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  exact eq_zero_of_restrictions m F hF hP hQ

/-- Lower-chart restriction on the entire actual covariant coordinate space. -/
def covariantRestriction (m : ℕ) :
    AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
      (characterCoordinate k ^ m) →ₗ[k] Polynomial k :=
  (lowerRestriction (k := k)).toLinearMap.comp
    ((coordinateAlgEquiv (Fin 2) k).symm.toLinearMap.comp
      (AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m)).subtype)

/-- Lower-chart restriction is injective on the entire covariant space. -/
theorem covariantRestriction_injective (m : ℕ) :
    Function.Injective (covariantRestriction (k := k) m) := by
  intro F G h
  have hzero : covariantRestriction (k := k) m (F - G) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem : coordinateAlgEquiv (Fin 2) k
      ((coordinateAlgEquiv (Fin 2) k).symm ((F - G).val)) ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m) := by
    simpa only [AlgEquiv.apply_symm_apply] using (F - G).property
  have hz := eq_zero_of_lowerRestriction m _ hmem hzero
  have hz' : F - G = 0 := by
    apply Subtype.ext
    change (F - G).val = 0
    have e := congrArg (coordinateAlgEquiv (Fin 2) k) hz
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using e
  exact sub_eq_zero.mp hz'

open HomogeneousPolynomial

/-- A binary monomial restricts to the corresponding power of the chart coordinate. -/
theorem covariantRestriction_binaryBasis (m : ℕ) (c : Fin (m + 1)) :
    covariantRestriction (k := k) m (covariantRowMap k m (binaryBasis m c)) =
      Polynomial.X ^ c.val := by
  change lowerRestriction
    ((coordinateAlgEquiv (Fin 2) k).symm
      (coordinateAlgEquiv (Fin 2) k (rowPolynomial 1 (binaryBasis m c).val))) = _
  rw [AlgEquiv.symm_apply_apply]
  change classify (lowerChart (Polynomial.X : Polynomial k))
    (rowPolynomial 1 (binaryBasis m c).val) = _
  rw [classify_rowPolynomial, aeval_binaryBasis]
  simp [lowerChart]

/-- Every actual covariant coordinate is a homogeneous bottom-row polynomial. -/
theorem covariantRowMap_surjective (m : ℕ) : Function.Surjective (covariantRowMap k m) := by
  intro F
  let P := covariantRestriction (k := k) m F
  let f : homogeneousSubmodule (Fin 2) k m :=
    ∑ c : Fin (m + 1), P.coeff c.val • binaryBasis m c
  refine ⟨f, covariantRestriction_injective m ?_⟩
  change covariantRestriction (k := k) m
    (covariantRowMap k m (∑ c : Fin (m + 1), P.coeff c.val • binaryBasis m c)) = P
  simp only [map_sum, map_smul, covariantRestriction_binaryBasis, Polynomial.smul_eq_C_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => Polynomial.C (P.coeff i) * Polynomial.X ^ i)]
  apply Eq.symm
  apply Polynomial.as_sum_range_C_mul_X_pow'
  have hmem : coordinateAlgEquiv (Fin 2) k
      ((coordinateAlgEquiv (Fin 2) k).symm F.val) ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m) := by
    simpa only [AlgEquiv.apply_symm_apply] using F.property
  exact Nat.lt_succ_of_le (lowerRestriction_natDegree_le m _ hmem)

/-- The full binary homogeneous polynomial module is the entire actual covariant space. -/
def covariantRowEquiv (m : ℕ) : homogeneousSubmodule (Fin 2) k m ≃ₗ[k]
    AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
      (characterCoordinate k ^ m) :=
  LinearEquiv.ofBijective (covariantRowMap k m)
    ⟨covariantRowMap_injective k m, covariantRowMap_surjective m⟩

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
