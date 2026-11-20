import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalizationBaseChangeReduced
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.CommutativeAlgebra.IntegralClosureTransfer

/-! # Reduced normalized residue fibres and the vertical local test -/

open IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Congruence

variable {S D E : Type*} [CommRing S] [CommRing D] [CommRing E] [Algebra S D] [Algebra S E]

/-- An algebra isomorphism over the DVR induces an isomorphism of the
normalizations in the generic fibres. -/
def genericNormalizationCongr (e : D ≃ₐ[S] E) :
    integralClosure D (D ⊗[S] FractionRing S) ≃ₐ[S] integralClosure E (E ⊗[S] FractionRing S) := by
  let f := Algebra.TensorProduct.congr e (AlgEquiv.refl : FractionRing S ≃ₐ[S] FractionRing S)
  let g := Langlands.CommutativeAlgebra.IntegralClosureTransfer.integralClosureEquiv
    e.toRingEquiv f.toRingEquiv (fun _ => rfl)
  exact { g with commutes' := fun s => Subtype.ext (f.commutes s) }

end Congruence

section MaximalIdeals

variable (R S B C : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)] [CommRing C] [Algebra B C] [Algebra S C]
    [Algebra.IsIntegral B C]

/-- In a local normalization over a vertical DVR, the primes containing
the extended base uniformizer are exactly the maximal ideals. -/
theorem mem_baseUniformizer_iff_isMaximal
    (hinjS : Function.Injective (algebraMap R S)) (hinjB : Function.Injective (algebraMap R B))
    (hcompat : ∀ r, algebraMap B C (algebraMap R B r) = algebraMap S C (algebraMap R S r))
    {t : S} (ht : Irreducible t) (J : Ideal C) [J.IsPrime] :
    algebraMap S C t ∈ J ↔ J.IsMaximal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ hinjS).mpr hπ.ne_zero) ht
  have hn : 0 < n := by
    by_contra h
    have hunit : IsUnit (algebraMap R S π) := by
      simpa only [hv, Nat.eq_zero_of_not_pos h, pow_zero, mul_one] using v.isUnit
    exact hπ.not_isUnit (IsLocalHom.map_nonunit (f := algebraMap R S) _ hunit)
  have hmem : algebraMap R B π ∈ J.under B ↔ algebraMap S C t ∈ J := by
    change algebraMap B C (algebraMap R B π) ∈ J ↔ _
    rw [hcompat, hv, map_mul, map_pow, Ideal.unit_mul_mem_iff_mem J (v.isUnit.map _),
      (inferInstance : J.IsPrime).pow_mem_iff_mem _ hn]
  constructor
  · intro hJ
    have hne : J.under B ≠ ⊥ := by
      intro h
      exact (map_ne_zero_iff _ hinjB).mpr hπ.ne_zero (Ideal.mem_bot.mp (h ▸ hmem.mpr hJ))
    have : (J.under B).IsPrime := inferInstance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under J (this.isMaximal hne)
  · intro hJ
    have hJ' : (J.under B).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal J
    apply hmem.mp
    rw [IsLocalRing.eq_maximalIdeal hJ', IsLocalRing.mem_maximalIdeal]
    exact fun h => hπ.not_isUnit (IsLocalHom.map_nonunit (f := algebraMap R B) _ h)

end MaximalIdeals

section NormalizedResidue

variable (R S Q : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q] [Algebra R Q]
    [IsLocalHom (algebraMap R Q)]

local notation "D" => S ⊗[R] Q
local notation "G" => D ⊗[S] FractionRing S
local notation "C" => integralClosure D G
local instance : CommRing C := @Subalgebra.toCommRing D G _ _ _ C
local instance : Algebra Q D := Algebra.TensorProduct.rightAlgebra
local instance : IsScalarTower R Q D := Algebra.TensorProduct.right_isScalarTower
local instance : Algebra Q C := Algebra.compHom C (algebraMap Q D)

/-- The normalized residue tensor at a vertical DVR yields the test at its
maximal localizations if it is reduced, for a finite extension of the base. -/
theorem uniformizerAtMaximalLocalizations_of_reduced_normalizedResidue
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    {t : S} (ht : Irreducible t) (hred : IsReduced (ResidueField S ⊗[S] C)) :
    UniformizerAtMaximalLocalizations C (algebraMap S C t) := by
  have : Module.Finite Q D := Module.Finite.equiv (Algebra.TensorProduct.commRight R Q S).toLinearEquiv
  have : IsScalarTower Q D C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral Q C := ⟨fun x => isIntegral_trans (R := Q) (A := D) x
    (Algebra.IsIntegral.isIntegral x)⟩
  have hcompat (r : R) : algebraMap Q C (algebraMap R Q r) =
      algebraMap S C (algebraMap R S r) := by
    rw [IsScalarTower.algebraMap_apply Q D C, IsScalarTower.algebraMap_apply S D C,
      ← IsScalarTower.algebraMap_apply R Q D, ← IsScalarTower.algebraMap_apply R S D]
  have hred' : IsReduced (C ⧸ Ideal.span {algebraMap S C t}) := by
    let e := residueTensorEquivPrincipalQuotient S C ht.maximalIdeal_eq
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  apply uniformizerAtMaximalLocalizations_of_isReduced_principalQuotient hred'
  · intro J hJ
    have : J.IsPrime := hJ.isPrime
    exact (mem_baseUniformizer_iff_isMaximal R S Q C hinjS hinjQ hcompat ht J).mpr hJ
  · intro J hJ hmem
    exact (mem_baseUniformizer_iff_isMaximal R S Q C hinjS hinjQ hcompat ht J).mp hmem

end NormalizedResidue

section LocalComparison

variable (R S B G : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [CommRing B] [Algebra R B]
    [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]
    (p : Ideal B) [p.IsPrime]

local notation "Q" => Localization.AtPrime p
local notation "D" => S ⊗[R] Q
local notation "Gₚ" => Q ⊗[B] G
local notation "H" => S ⊗[R] Gₚ
local notation "H₀" => D ⊗[S] FractionRing S
local instance : Algebra R Gₚ := Algebra.TensorProduct.leftAlgebra
local instance : IsScalarTower R Q Gₚ := TensorProduct.isScalarTower_left
local instance : Algebra D H := tensorBaseChangeAlgebra R S Q (B := Gₚ)
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S Q (B := Gₚ)

set_option maxHeartbeats 1000000 in
private def localizedGenericFibreEquiv
    (hinj : Function.Injective (algebraMap R S))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G) :
    H ≃ₐ[D] H₀ := by
  let t := Classical.choose (IsDiscreteValuationRing.exists_irreducible S)
  have ht : Irreducible t := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible S)
  have hGₚ : IsLocalization (Algebra.algebraMapSubmonoid Q (nonZeroDivisors R)) Gₚ := by
    let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
    have : IsLocalization M G := hloc
    have h := IsLocalization.tensor (S := Q) G M
    simpa only [M, Algebra.algebraMapSubmonoid_map_map] using h
  have hH : IsLocalization.Away (algebraMap S D t) H :=
    isLocalizationAway_tensor_of_localDvrMap R S Q Gₚ hinj ht hGₚ
  have := Langlands.AlgebraicGeometry.isLocalizationAway_fractionRing_of_dvr
    S (FractionRing S) ht
  have hH₀ : IsLocalization.Away (algebraMap S D t) H₀ := IsLocalization.Away.tensor ..
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap S D t)) H H₀

/-- At an original prime of the normalized algebra, the local tensor
normalization is the normalization of the base-changed local ring in its
generic fibre. -/
def localTensorNormalizationGenericEquiv
    (hinj : Function.Injective (algebraMap R S))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G) :
    localTensorNormalization R S B G p ≃+* integralClosure D H₀ :=
  (localTensorNormalizationEquiv R S B G p).trans
    (localizedGenericFibreEquiv R S B G p hinj hloc).mapIntegralClosure.toRingEquiv

set_option maxHeartbeats 1000000 in
theorem localTensorNormalizationGenericEquiv_baseMap
    (hinj : Function.Injective (algebraMap R S))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G) (t : S) :
    localTensorNormalizationGenericEquiv R S B G p hinj hloc
        (localTensorNormalizationBaseMap R S B G p t) = algebraMap S (integralClosure D H₀) t := by
  let e := localizedGenericFibreEquiv R S B G p hinj hloc
  let f : integralClosure D H ≃+* integralClosure D H₀ :=
    (AlgEquiv.mapIntegralClosure (R := D) (A := H) (S := H₀) e).toRingEquiv
  exact (congrArg f (localTensorNormalizationEquiv_baseMap R S B G p t)).trans
    (Subtype.ext (e.commutes (algebraMap S D t)))

end LocalComparison

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
