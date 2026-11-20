import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.LocalTensorComparison
import Langlands.CommutativeAlgebra.FlatDvrNormality

/-! # Normalization and reduced principal fibres under residue-preserving base change -/

open IsLocalRing TensorProduct
open Langlands.CommutativeAlgebra.FlatDvrNormality

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Principal

variable (C H : Type*) [CommRing C] [CommRing H] [Algebra C H]

/-- A regular element with a reduced principal quotient can be inverted
without adding any new elements integral over the original ring. -/
def algebraEquivIntegralClosure_of_reduced_principalQuotient
    (x : C) [IsLocalization.Away x H] (hx : x ∈ nonZeroDivisors C)
    (hred : IsReduced (C ⧸ Ideal.span {x})) :
    C ≃ₐ[C] integralClosure C H := by
  have hinj : Function.Injective (algebraMap C H) :=
    IsLocalization.injective H (Submonoid.powers_le.mpr hx)
  apply AlgEquiv.ofBijective (Algebra.ofId C (integralClosure C H))
  constructor
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · intro b
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x b.val
    obtain ⟨c, hc⟩ := mem_range_of_isIntegral_of_pow_mul hinj
      (IsLocalization.Away.algebraMap_isUnit x).isRegular.left hred n b.property
      ⟨a, by rw [mul_comm]; exact ha.symm⟩
    exact ⟨c, Subtype.ext hc⟩

variable {C}

/-- The uniformizer test at all maximal ideals implies reducedness of the
principal quotient. -/
theorem isReduced_principalQuotient_of_uniformizerAtMaximalLocalizations {x : C}
    (h : UniformizerAtMaximalLocalizations C x) : IsReduced (C ⧸ Ideal.span {x}) := by
  let I := Ideal.span {x}
  apply isReduced_ofLocalizationMaximal
  intro q hq
  have : q.IsPrime := hq.isPrime
  let J := q.comap (Ideal.Quotient.mk I)
  have hJ : J.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have : J.IsPrime := hJ.isPrime
  let T := Localization.AtPrime J
  have hI : I.map (algebraMap C T) = maximalIdeal T := by
    rw [show I = Ideal.span {x} from rfl, Ideal.map_span, Set.image_singleton]
    exact h J hJ
  let e := (localizationAtPrimeQuotientEquiv I q).toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  exact isReduced_of_injective e.toRingHom e.injective

/-- If every maximal ideal contains the scalar and every prime containing
the scalar is maximal, reducedness of the principal quotient gives the
uniformizer test. -/
theorem uniformizerAtMaximalLocalizations_of_isReduced_principalQuotient {x : C}
    (hred : IsReduced (C ⧸ Ideal.span {x}))
    (hcontain : ∀ (J : Ideal C), J.IsMaximal → x ∈ J)
    (hmax : ∀ (J : Ideal C), J.IsPrime → x ∈ J → J.IsMaximal) :
    UniformizerAtMaximalLocalizations C x := by
  intro J hJ
  have : J.IsPrime := hJ.isPrime
  let I := Ideal.span {x}
  let T := Localization.AtPrime J
  have hmin : I.IsMinimalPrime J := by
    refine ⟨⟨inferInstance, J.span_singleton_le_iff_mem.mpr (hcontain J hJ)⟩, ?_⟩
    intro q hq hqJ
    have hqmax := hmax q hq.1 (hq.2 (Ideal.mem_span_singleton_self x))
    exact (hqmax.eq_of_le hJ.ne_top hqJ).ge
  have hmap := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes T J I hmin
  have hredT := isReduced_localization_quotient hred J
  have hI : I.map (algebraMap C T) =
      Ideal.span {algebraMap C T x} := by rw [show I = Ideal.span {x} from rfl,
    Ideal.map_span, Set.image_singleton]
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal J T, hI] at hmap
  exact ((Ideal.isRadical_iff_quotient_reduced _).mpr hredT).radical.symm.trans hmap

end Principal

section Residue

variable (R S C : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [CommRing C] [Algebra R C]

/-- The residue tensor of a base change agrees with the original residue
tensor when the local base extension preserves its residue field. -/
def residueTensorBaseChangeRingEquiv
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S))) :
    ResidueField S ⊗[S] (S ⊗[R] C) ≃+* ResidueField R ⊗[R] C := by
  let f : ResidueField R ≃ₐ[R] ResidueField S :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField S))
      ⟨(algebraMap (ResidueField R) (ResidueField S)).injective, hres⟩
  let e := Algebra.TensorProduct.cancelBaseChange R S (ResidueField S) (ResidueField S) C
  exact e.toRingEquiv.trans (Algebra.TensorProduct.congr f.symm (AlgEquiv.refl : C ≃ₐ[R] C)).toRingEquiv

end Residue

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
