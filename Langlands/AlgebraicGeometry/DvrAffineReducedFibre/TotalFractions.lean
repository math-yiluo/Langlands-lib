import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Langlands.CommutativeAlgebra.RegularLocalFactorialProof
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-! # Comparing normalization in the generic fibre and in the total fraction ring -/

open AlgebraicGeometry CategoryTheory IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- Integral closedness in the total fraction ring follows from normality at
the localizations at maximal ideals. -/
theorem isIntegrallyClosed_of_normal_maximalLocalizations {B : Type*} [CommRing B]
    (hNormal : ∀ (p : Ideal B) [p.IsMaximal],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed B := by
  rw [isIntegrallyClosed_iff (FractionRing B)]
  intro x hx
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors B) x
  let I := Ideal.span {(s : B)}
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) I
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hJp⟩ := J.exists_le_maximal hne
    let Bp := Localization.AtPrime p
    let L := FractionRing Bp
    obtain ⟨hDomain, hClosed⟩ := hNormal p
    have hu (t : nonZeroDivisors B) : IsUnit (algebraMap B L t) := by
      rw [IsScalarTower.algebraMap_apply B Bp L]
      exact IsLocalization.map_units (M := nonZeroDivisors Bp) L
        ⟨_, IsLocalization.map_nonZeroDivisors_le p.primeCompl Bp ⟨t, t.2, rfl⟩⟩
    let g : FractionRing B →ₐ[B] L :=
      IsLocalization.liftAlgHom (f := Algebra.ofId B L) hu
    have hint : IsIntegral Bp (g (IsLocalization.mk' (FractionRing B) b s)) :=
      IsIntegral.tower_top (A := Bp) (hx.map g)
    obtain ⟨v, hv⟩ := (isIntegrallyClosed_iff L).mp hClosed hint
    have hmul :
        algebraMap Bp L v * algebraMap B L s = algebraMap B L b := by
      rw [hv, ← g.commutes (s : B), ← map_mul, IsLocalization.mk'_spec, g.commutes]
    have hmem : algebraMap B Bp b ∈ I.map (algebraMap B Bp) := by
      rw [show I = Ideal.span {(s : B)} from rfl, Ideal.map_span, Set.image_singleton]
      refine Ideal.mem_span_singleton'.mpr ⟨v, IsFractionRing.injective Bp L ?_⟩
      rw [map_mul, ← IsScalarTower.algebraMap_apply, hmul, ← IsScalarTower.algebraMap_apply]
    obtain ⟨t, ht, htb⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl Bp I b).mp hmem
    exact ht (hJp htb)
  have hb : b ∈ I := by
    have h1 : (1 : B) ∈ J := by simp [hJ]
    change (1 : B) * b ∈ I at h1
    simpa using h1
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hb
  exact ⟨v, IsLocalization.eq_mk'_iff_mul_eq.mpr (by rw [← map_mul, hv])⟩

/-- A smooth algebra over a field is integrally closed in its total fraction ring. -/
theorem isIntegrallyClosed_of_smooth_over_field (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [Algebra.Smooth K B] : IsIntegrallyClosed B := by
  let f := Spec.algebraMap K B
  have : Smooth f := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  apply isIntegrallyClosed_of_normal_maximalLocalizations
  intro p hp
  let x : PrimeSpectrum B := ⟨p, hp.isPrime⟩
  let C := (Spec (.of B)).presheaf.stalk x
  have hReg : IsRegularLocalRing C := AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := f) x
  have : IsDomain C := IsRegularLocalRing.isDomainFLT C
  have := Langlands.CommutativeAlgebra.regularLocalFactorial C hReg
  have hClosed : IsIntegrallyClosed C := inferInstance
  let e := (Spec.stalkIso (.of B) x).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain, hClosed.of_equiv e⟩

section Generic

variable (S D : Type u) [CommRing S] [CommRing D] [Algebra S D] [Module.Flat S D]

local notation "G" => D ⊗[S] FractionRing S
local notation "S₀" => Algebra.algebraMapSubmonoid D (nonZeroDivisors S)

private lemma genericDenominators_regular : S₀ ≤ nonZeroDivisors D := by
  rintro _ ⟨s, hs, rfl⟩
  apply mem_nonZeroDivisors_iff_left.mpr
  intro d hd
  have hregular : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors hs
  exact hregular (show s • d = s • (0 : D) by rw [Algebra.smul_def, hd, smul_zero])

/-- Embedding of the generic localization into the total fraction ring of the
original algebra. -/
def genericFibreTotalFractionsMap : G →ₐ[D] FractionRing D :=
  IsLocalization.liftAlgHom (f := Algebra.ofId D (FractionRing D))
    fun t : S₀ => IsLocalization.map_units (M := nonZeroDivisors D) (FractionRing D)
      ⟨t, genericDenominators_regular S D t.2⟩

theorem genericFibreTotalFractionsMap_injective :
    Function.Injective (genericFibreTotalFractionsMap S D) := by
  let e := genericFibreTotalFractionsMap S D
  apply (IsLocalization.injective_iff_map_algebraMap_eq S₀ e.toRingHom).mpr
  intro x y
  change algebraMap D G x = algebraMap D G y ↔
    e (algebraMap D G x) = e (algebraMap D G y)
  simp only [AlgHom.commutes,
    (IsLocalization.injective G (genericDenominators_regular S D)).eq_iff,
    (IsFractionRing.injective D (FractionRing D)).eq_iff]

/-- If the generic localization is integrally closed, the integral closures of
the original algebra in that localization and in its total fraction ring agree. -/
def integralClosureGenericFibreEquivTotalFractions [IsIntegrallyClosed G] :
    integralClosure D G ≃ₐ[D] integralClosure D (FractionRing D) := by
  let e := genericFibreTotalFractionsMap S D
  letI : Algebra G (FractionRing D) := e.toRingHom.toAlgebra
  have : IsScalarTower D G (FractionRing D) :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  have : IsFractionRing G (FractionRing D) :=
    IsFractionRing.isFractionRing_of_isLocalization S₀ G (FractionRing D)
      (genericDenominators_regular S D)
  refine AlgEquiv.ofBijective e.mapIntegralClosure ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (genericFibreTotalFractionsMap_injective S D (congrArg Subtype.val hxy))
  · intro x
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (FractionRing D)).mp ‹IsIntegrallyClosed G›
      (IsIntegral.tower_top (A := G) x.2)
    have hy' : e y = (x : FractionRing D) := hy
    exact ⟨⟨y, (isIntegral_algHom_iff e (genericFibreTotalFractionsMap_injective S D)).mp
      (hy'.symm ▸ x.2)⟩, Subtype.ext hy'⟩

end Generic

/-- The generic fibre of a smooth algebra over the fraction field of a
domain is integrally closed, with the fraction field on the right of the tensor product. -/
theorem isIntegrallyClosed_genericFibre (S D : Type u) [CommRing S] [IsDomain S]
    [CommRing D] [Algebra S D]
    [Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D)] :
    IsIntegrallyClosed (D ⊗[S] FractionRing S) := by
  let K := FractionRing S
  let : Algebra K (D ⊗[S] K) := Algebra.TensorProduct.rightAlgebra
  let e : K ⊗[S] D ≃ₐ[K] D ⊗[S] K :=
    { (Algebra.TensorProduct.comm S K D).toRingEquiv with
      commutes' := fun k => Algebra.TensorProduct.comm_tmul S k 1 }
  have : Algebra.Smooth K (D ⊗[S] K) := Algebra.Smooth.of_equiv e
  exact isIntegrallyClosed_of_smooth_over_field K (D ⊗[S] K)

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
