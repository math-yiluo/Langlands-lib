import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.CuspidalWhittakerExpansionProof
import Langlands.Global.RankinSelberg.WhittakerQuotientScaling
import Langlands.Representation.RestrictedTensor.LocalSeparation

/-! # Nonzero spherical vectors and positive quotient measure for self-pairs -/

noncomputable section
universe u uV
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open Automorphic FiniteAdelicGL Langlands.RestrictedTensor

local instance positiveDataSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance positiveDataSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance {n : ℕ} (A : FiniteRealization F n) : AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- A supplied genuine tensor presentation contains a nonzero vector spherical
outside every finite set containing its spectral exceptional set. -/
theorem exists_sphericalOutside_ne_zero {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uV} T)
    {S : Finset (FinitePlace F)} (hPS : P.exceptional ⊆ S) :
    ∃ x : T.Space, x ≠ 0 ∧ IsSphericalOutside F T S x := by
  classical
  let E := P.tensorExceptional
  let ρ := fun v => (P.localFactor v).representation
  choose y hy using fun v : E =>
    P.presentation.exists_nonzero_localFactor P.finiteSlice.nonzero v.val
  let z := pure (K := ℂ) E P.reference ⟨E, le_rfl⟩ y
  have hz : z ≠ 0 := by
    intro h
    apply stage_tprod_ne_zero (K := ℂ) (V := fun v => P.localFactor v) E y hy
    apply of_injective (K := ℂ) (V := fun v => P.localFactor v)
      E P.reference P.presentation.reference_nonzero ⟨E, le_rfl⟩
    simpa only [z, Langlands.RestrictedTensor.pure, map_zero] using h
  let tensorMap : (tensorRepresentation F (r + 1) ρ E P.reference P.reference_fixed).IntertwiningMap
      T.realization.finiteRepresentation :=
    T.realization.finiteEquiv.symm.toIntertwiningMap.comp
      (P.finiteSlice.inclusion.comp P.presentation.equiv.toIntertwiningMap)
  have htensorMap : Function.Injective tensorMap :=
    T.realization.finiteEquiv.symm.injective.comp
      (P.finiteSlice.inclusion_injective.comp P.presentation.equiv.injective)
  refine ⟨tensorMap z, fun h => hz (htensorMap (h.trans (map_zero tensorMap).symm)), ?_⟩
  intro v hv k hk
  have hvE : v ∉ E := fun hv' => hv (hPS (P.unramified.exceptional_subset hv'))
  have hact :
      tensorRepresentation F (r + 1) ρ E P.reference P.reference_fixed
        (localInclusion F (r + 1) v k) z = z := by
    have hlocal : ∀ w ∉ E,
        localProjection F (r + 1) w (localInclusion F (r + 1) v k) ∈
          localIntegral F (r + 1) w := by
      intro w _
      by_cases hw : w = v
      · subst w
        rwa [localProjection_localInclusion]
      · rw [localProjection_localInclusion_of_ne F (r + 1) v w hw]
        exact (localIntegral F (r + 1) w).one_mem
    rw [show z = pure (K := ℂ) E P.reference ⟨E, le_rfl⟩ y from rfl,
      tensorRepresentation_pure_of_mem F (r + 1) ρ E P.reference P.reference_fixed
        _ ⟨E, le_rfl⟩ hlocal]
    congr 1
    funext w
    have hw : w.val ≠ v := fun h => hvE (h ▸ w.property)
    rw [localProjection_localInclusion_of_ne F (r + 1) v w hw,
      map_one, Module.End.one_apply]
  exact (LinearMap.congr_fun (tensorMap.isIntertwining' _) z).symm.trans (congrArg tensorMap hact)

/-- Every nonzero cuspidal vector has a nonzero global Whittaker coefficient. -/
theorem exists_cuspWhittaker_ne_zero {r : ℕ} (T : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {x : T.Space} (hx : x ≠ 0) :
    ∃ g : Points F (r + 1), cuspWhittaker F T ψ x g ≠ 0 := by
  by_contra! hW
  apply hx
  apply Unfolding.cuspLinear_injective F T
  have hφ : cuspFunction F T x = 0 := by
    funext g
    have hsum : HasSum (fun _ : UnipotentRationalCosets F r => (0 : ℂ))
        (cuspFunction F T x g) := by
      simpa only [hW] using
        (cuspidalWhittakerExpansionStatement_proof F r T ψ hψ x g).2
    exact hsum.unique hasSum_zero
  exact hφ.trans (map_zero (Unfolding.cuspLinear F T)).symm

/-- The quotient measure used in the Whittaker integral is positive on every
nonempty open set. -/
theorem isOpenPosMeasure_whittakerQuotientMeasure (n : ℕ) :
    (whittakerQuotientMeasure F n).IsOpenPosMeasure := by
  classical
  let quotientMeasure := whittakerQuotientMeasure F n
  let : quotientMeasure.Regular := WhittakerQuotientScaling.regular_whittakerQuotientMeasure F n
  obtain ⟨K, hK, hμK⟩ :=
    Measure.Regular.exists_isCompact_not_null.mpr
      (WhittakerQuotientScaling.whittakerQuotientMeasure_ne_zero F n)
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨q, hq⟩ := hne
  obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective (unipotentAdelic F n) q
  have hcover : K ⊆ ⋃ g : Points F n,
      LeftCosetSpace.rightTranslate (unipotentAdelic F n) g ⁻¹' U := by
    intro q _
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (unipotentAdelic F n) q
    refine Set.mem_iUnion.mpr ⟨x⁻¹ * u, ?_⟩
    simpa only [Set.mem_preimage, LeftCosetSpace.rightTranslate_mk,
      mul_inv_cancel_left] using hq
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : Points F n => LeftCosetSpace.rightTranslate (unipotentAdelic F n) g ⁻¹' U)
    (fun g => hU.preimage (LeftCosetSpace.continuous_rightTranslate _ g)) hcover
  intro hzero
  apply hμK
  apply measure_mono_null ht
  apply (measure_biUnion_null_iff t.countable_toSet).mpr
  intro g _
  exact ((WhittakerQuotientScaling.measurePreserving_rightTranslate F n g).measure_preimage
    hU.measurableSet.nullMeasurableSet).trans hzero

/-- Internal existence statement for the spherical Whittaker data used in
self-pair positivity. The presentation is supplied, rather than postulated. -/
def SphericalWhittakerNonvanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{u, uV} T) (S : Finset (FinitePlace K)),
    P.exceptional ⊆ S →
    ∀ (ψ : AddChar (Adeles K) ℂ), IsStandardAdditiveCharacter K ψ →
    ∃ (x : T.Space) (g : Points K (r + 1)),
      x ≠ 0 ∧ IsSphericalOutside K T S x ∧ cuspWhittaker K T ψ x g ≠ 0

/-- Proof from the actual tensor presentation and the cuspidal Whittaker
expansion. -/
theorem sphericalWhittakerNonvanishing :
    SphericalWhittakerNonvanishingStatement.{u, uV} := by
  intro K _ _ _ r T P S hPS ψ hψ
  obtain ⟨x, hx, hxS⟩ := exists_sphericalOutside_ne_zero P hPS
  obtain ⟨g, hg⟩ := exists_cuspWhittaker_ne_zero T ψ hψ hx
  exact ⟨x, g, hx, hxS, hg⟩

end Langlands.Global.RankinSelbergGlobal.SelfPair
