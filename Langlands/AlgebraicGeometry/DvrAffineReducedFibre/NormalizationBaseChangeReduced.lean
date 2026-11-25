import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.ResiduePreservingNormalization

/-! # Normalization after a residue-preserving extension of DVRs -/

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Uniformizers

variable (R D H : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing D] [Algebra R D] [CommRing H] [Algebra D H]

private theorem isLocalizationAway_of_invertingNonzeroDvr {π : R} (hπ : Irreducible π)
    (h : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) H) :
    IsLocalization.Away (algebraMap R D π) H := by
  let M := Submonoid.powers (algebraMap R D π)
  let N := Algebra.algebraMapSubmonoid D (nonZeroDivisors R)
  have hle : M ≤ N :=
    Submonoid.powers_le.mpr (Algebra.mem_algebraMapSubmonoid_of_mem
      ⟨π, mem_nonZeroDivisors_of_ne_zero hπ.ne_zero⟩)
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := H) M N hle ?_).mpr h
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
  refine ⟨algebraMap R D π ^ n, ⟨n, rfl⟩, ?_⟩
  rw [← map_pow]
  apply map_dvd
  rw [hu]
  exact (associated_unit_mul_left (π ^ n) (u : R) u.isUnit).dvd

end Uniformizers

section TensorLocalization

variable (R S B G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [CommRing B] [Algebra R B]
    [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]

local notation "D" => S ⊗[R] B
local notation "H" => S ⊗[R] G
local instance : Algebra D H := tensorBaseChangeAlgebra R S B (B := G)
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S B (B := G)

/-- Extending the DVR base of a generic localization gives the localization
away from the new uniformizer. -/
theorem isLocalizationAway_tensor_of_localDvrMap
    (hinj : Function.Injective (algebraMap R S)) {t : S} (ht : Irreducible t)
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G) :
    IsLocalization.Away (algebraMap S D t) H := by
  let M := nonZeroDivisors R
  let M₀ := Algebra.algebraMapSubmonoid B M
  let j : B →ₐ[R] D := Algebra.TensorProduct.includeRight
  have hlocD : IsLocalization (M₀.map j) H := by
    have : IsLocalization M₀ G := hloc
    apply IsLocalization.tensorProduct_tensorProduct_right R S M₀ G
    ext x
    rfl
  have hlocR : IsLocalization (Algebra.algebraMapSubmonoid D M) H := by
    simpa only [j, M₀, Algebra.algebraMapSubmonoid_map_eq] using hlocD
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away (algebraMap R D π) H :=
    isLocalizationAway_of_invertingNonzeroDvr R D H hπ hlocR
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero) ht
  have hn : 0 < n := by
    by_contra h
    have hunit : IsUnit (algebraMap R S π) := by
      simpa only [hu, Nat.eq_zero_of_not_pos h, pow_zero, mul_one] using u.isUnit
    exact hπ.not_isUnit (IsLocalHom.map_nonunit (f := algebraMap R S) _ hunit)
  let x := algebraMap S D t
  have hAssoc : Associated (algebraMap R D π) (x ^ n) := by
    rw [IsScalarTower.algebraMap_apply R S D, hu, map_mul, map_pow]
    exact associated_unit_mul_left _ _ (u.isUnit.map (algebraMap S D))
  have hpow : IsLocalization.Away (x ^ n) H := IsLocalization.Away.of_associated hAssoc
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := H) (Submonoid.powers (x ^ n))
    (Submonoid.powers x) (Submonoid.powers_le.mpr ⟨n, rfl⟩) ?_).mp hpow
  rintro _ ⟨m, rfl⟩
  exact ⟨(x ^ n) ^ m, ⟨m, rfl⟩,
    pow_mul x n m ▸ pow_dvd_pow x (Nat.le_mul_of_pos_left m hn)⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [IsLocalHom (algebraMap R S)] in
private theorem nonZeroDivisor_tensor_of_localizationAway [Module.Flat R S]
    (hBG : Function.Injective (algebraMap B G)) (x : D)
    (hloc : IsLocalization.Away x H) : x ∈ nonZeroDivisors D := by
  let f : B →ₐ[R] G := IsScalarTower.toAlgHom R B G
  have hDH : Function.Injective (algebraMap D H) := by
    change Function.Injective (LinearMap.lTensor S f.toLinearMap)
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hBG
  rw [mem_nonZeroDivisors_iff_left]
  intro y hy
  apply hDH
  rw [map_zero]
  have hy' := congrArg (algebraMap D H) hy
  rw [map_mul, map_zero] at hy'
  exact (IsLocalization.Away.algebraMap_isUnit x).mul_right_eq_zero.mp hy'

variable [Module.Flat R S]

/-- A ring with reduced residue tensor remains integrally closed in its generic
localization under a flat extension of DVRs preserving the residue field. -/
def tensorEquivIntegralClosure_of_reduced_residue
    (hinj : Function.Injective (algebraMap R S))
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (hBG : Function.Injective (algebraMap B G))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G)
    (hred : IsReduced (ResidueField R ⊗[R] B)) :
    D ≃ₐ[S] integralClosure D H := by
  let t := Classical.choose (IsDiscreteValuationRing.exists_irreducible S)
  have ht : Irreducible t := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible S)
  let x := algebraMap S D t
  have hxloc : IsLocalization.Away x H :=
    isLocalizationAway_tensor_of_localDvrMap R S B G hinj ht hloc
  have hx : x ∈ nonZeroDivisors D :=
    nonZeroDivisor_tensor_of_localizationAway R S B G hBG x hxloc
  let e := (residueTensorEquivPrincipalQuotient S D ht.maximalIdeal_eq).symm.trans
    (residueTensorBaseChangeRingEquiv R S B hres)
  have hred' : IsReduced (D ⧸ Ideal.span {x}) := isReduced_of_injective e.toRingHom e.injective
  exact (algebraEquivIntegralClosure_of_reduced_principalQuotient D H x hx hred').restrictScalars S

end TensorLocalization

section ReducedResidue

universe u

variable (R S A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] [CommRing A] [Algebra R A]

local notation "G" => A ⊗[R] FractionRing R
local notation "N" => integralClosure A G
local notation "Aₛ" => S ⊗[R] A
local notation "Nₛ" => integralClosure Aₛ (Aₛ ⊗[S] FractionRing S)
local notation "D" => S ⊗[R] N
local notation "H" => S ⊗[R] G
local instance : Algebra D H := tensorBaseChangeAlgebra R S N (B := G)
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S N (B := G)
local instance : CommRing (integralClosure D H) :=
  @Subalgebra.toCommRing D H _ _ _ (integralClosure D H)
local instance : Algebra S (integralClosure D H) :=
  Subalgebra.algebra' (R := D) (A := H) (R' := S) (integralClosure D H)

set_option maxHeartbeats 1000000 in
/-- If the original normalized residue fibre is reduced, an injective flat
local DVR extension preserving the residue field commutes with normalization
in the generic fibre. -/
def normalizationBaseChangeEquiv_of_reduced_residue
    (hinj : Function.Injective (algebraMap R S))
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (hred : IsReduced (ResidueField R ⊗[R] N)) :
    D ≃ₐ[S] Nₛ := by
  let g := tensorEquivIntegralClosure_of_reduced_residue R S N G hinj hres Subtype.val_injective
    (isLocalization_integralClosure_genericFibre R A) hred
  exact g.trans (normalizationTensorBaseChangeEquiv R S A hinj).symm

set_option maxHeartbeats 1000000 in
/-- The normalized residue fibre remains reduced after a residue-preserving
extension of DVRs. -/
theorem isReduced_residue_normalization_baseChange_of_reduced
    (hinj : Function.Injective (algebraMap R S))
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (hred : IsReduced (ResidueField R ⊗[R] N)) :
    IsReduced (ResidueField S ⊗[S] Nₛ) := by
  have : NonUnitalNonAssocSemiring Nₛ := inferInstance
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl : ResidueField S ≃ₐ[ResidueField S] ResidueField S)
    (normalizationBaseChangeEquiv_of_reduced_residue R S A hinj hres hred).symm
  let f := e.toRingEquiv.trans (residueTensorBaseChangeRingEquiv R S N hres)
  exact isReduced_of_injective f.toRingHom f.injective

end ReducedResidue

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
