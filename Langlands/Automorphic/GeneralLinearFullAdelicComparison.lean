import Langlands.Automorphic.GeneralLinearCanonicalUniformComparison
import Langlands.Automorphic.GroupSchemeAmbientCompactOpen
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthProof
import Langlands.Automorphic.GroupSchemeConstantTermEnvelopingProof
import Langlands.Automorphic.GroupSchemeCuspidalEnvelopingAction
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthProof

/-! # Actual adelic forms and the full original general-linear operator spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme
open scoped CompactOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "std" => MatrixRepresentation.standard (Fin n) (CommRingCat.of F)
local notation "hG" => isConnectedReductive_generalLinear F (Fin n)
local notation "hsmooth" => IsConnectedReductive.smoothDimension_spec hG
local notation "hcalc" => adelicDifferentialCommutator_of_smooth F GLG hsmooth
local notation "hK" => generalLinearStandardInfiniteCompact_isMaximalCompact F n

local instance : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

private local instance : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

private local instance : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

private local instance : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

private local instance : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _

private local instance : AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- Every original matrix form has one global exponent for all enveloping derivatives,
computed using the height of any closed matrix embedding of positive size. -/
theorem generalLinearAutomorphicForm_uniformGrowth {N : ℕ}
    (rho : MatrixRepresentation GLG (Fin N)) (hrho : IsClosedSubgroup rho) (hN : 0 < N)
    (f : Langlands.Automorphic.AutomorphicForms F n) :
    IsGeneralLinearUniformGrowth F n rho f.val := by
  obtain ⟨g, hg⟩ := (finitePlotSmoothGeneralLinearEquiv F n).surjective f.val
  have hf := (Langlands.Automorphic.mem_automorphicSubrepresentation F n f.val).mp f.property
  have hslice : HasPolynomialGrowth F GLG rho g.val := by
    apply (mem_polynomialGrowthSubrepresentation F GLG rho g.val).mp
    apply (continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion
      F n rho hrho g.val).mp
    apply (Langlands.Automorphic.mem_polynomialGrowthSubrepresentation F n _).mpr
    rw [← finitePlotSmoothGeneralLinearEquiv_val, hg]
    exact hf.2.2.2
  have hmoderate := adelicSliceModerateGrowthStatement F GLG rho hG hrho hN
    g.val g.property.2 hslice
  have hform := (isActualAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth
    F n rho hsmooth hrho hN g).mpr ⟨by simpa only [hg] using hf, hmoderate⟩
  have huniform := adelicAutomorphicUniformGrowth F GLG (generalLinearStandardInfiniteCompact F n)
    rho hsmooth hG hrho hK hN g hform
  rw [← hg]
  exact (hasAdelicUniformPolynomialGrowth_iff_generalLinear F n hsmooth hcalc rho g).mp
    ((hasAdelicUniformModerateGrowth_iff F GLG rho hsmooth hcalc hN g).mp huniform)

/-- The uniform-growth realization contains the whole original operator space. -/
theorem uniformGeneralLinearOperatorRealization_eq_top {N : ℕ}
    (rho : MatrixRepresentation GLG (Fin N)) (hrho : IsClosedSubgroup rho) (hN : 0 < N) :
    uniformGeneralLinearOperatorRealization F n rho hN = ⊤ := by
  apply top_unique
  intro f _
  exact (mem_uniformGeneralLinearOperatorRealization_iff F n rho hN f).mpr
    (generalLinearAutomorphicForm_uniformGrowth F n rho hrho hN
      (Langlands.Automorphic.stableAutomorphicEquiv F n f))

/-- The actual uniform forms for the standard embedding are all the original forms,
via the published map on the same adelic function. -/
def canonicalUniformAdelicAutomorphicFormsEquiv (hn : 0 < n) :
    CanonicalUniformGeneralLinearAdelicForms F n hn ≃L[ℂ]
      Langlands.Automorphic.AutomorphicForms F n where
  toLinearEquiv :=
    { __ := uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc std
        (generalLinearStandard_isClosedSubgroup F n) hn hG
      invFun := fun f => ⟨(finitePlotSmoothGeneralLinearEquiv F n).symm f.val, by
        apply (mem_uniformAdelicAutomorphic_iff_generalLinear F n std hsmooth hcalc
          (generalLinearStandard_isClosedSubgroup F n) hn hG _).mpr
        rw [LinearEquiv.apply_symm_apply]
        exact ⟨f.property, generalLinearAutomorphicForm_uniformGrowth F n std
          (generalLinearStandard_isClosedSubgroup F n) hn f⟩⟩
      left_inv := fun f => Subtype.ext ((finitePlotSmoothGeneralLinearEquiv F n).symm_apply_apply
        f.val)
      right_inv := fun f => Subtype.ext ((finitePlotSmoothGeneralLinearEquiv F n).apply_symm_apply
        f.val) }
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (CompactOpen.continuous_generalLinearEquiv F n).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (CompactOpen.continuous_generalLinearEquiv_symm F n).comp
      (continuous_subtype_val.comp continuous_subtype_val)

@[simp]
theorem canonicalUniformAdelicAutomorphicFormsEquiv_val (hn : 0 < n)
    (f : CanonicalUniformGeneralLinearAdelicForms F n hn) :
    (canonicalUniformAdelicAutomorphicFormsEquiv F n hn f).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

@[simp]
theorem canonicalUniformAdelicAutomorphicFormsEquiv_symm_val (hn : 0 < n)
    (f : Langlands.Automorphic.AutomorphicForms F n) :
    ((canonicalUniformAdelicAutomorphicFormsEquiv F n hn).symm f).val =
      (finitePlotSmoothGeneralLinearEquiv F n).symm f.val := rfl

variable [CompactSpace (AdeleQuotient F)]

/-- The largest cuspidal realization already has uniform growth. -/
theorem uniformCuspidalGeneralLinearOperatorRealization_eq_cuspidal {N : ℕ}
    (rho : MatrixRepresentation GLG (Fin N)) (hrho : IsClosedSubgroup rho) (hN : 0 < N) :
    uniformCuspidalGeneralLinearOperatorRealization F n rho hN =
      cuspidalGeneralLinearOperatorRealization F n adelicConstantTermEnveloping := by
  rw [uniformCuspidalGeneralLinearOperatorRealization_eq F n adelicConstantTermEnveloping,
    uniformGeneralLinearOperatorRealization_eq_top F n rho hrho hN, top_inf_eq]

/-- The largest original cuspidal operator realization is equivalent to the actual uniform
cusp forms for the standard embedding. The forward map uses the original matrix function. -/
def canonicalCuspidalRealizationAdelicEquiv (hn : 0 < n) :
    (cuspidalGeneralLinearOperatorRealization F n adelicConstantTermEnveloping).Space ≃L[ℂ]
      CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn := by
  let S := cuspidalGeneralLinearOperatorRealization F n adelicConstantTermEnveloping
  have hS : S ≤ uniformGeneralLinearOperatorRealization F n std hn := by
    rw [uniformGeneralLinearOperatorRealization_eq_top F n std
      (generalLinearStandard_isClosedSubgroup F n) hn]
    exact le_top
  have hc : S.IsCuspidal :=
    cuspidalGeneralLinearOperatorRealization_isCuspidal F n adelicConstantTermEnveloping
  let inverse (f : CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn) : S.Space := by
    obtain ⟨hf, hcuspidal⟩ :=
      (mem_canonicalUniformGeneralLinearAdelicCuspidalForms_iff F n hn f.val).mp f.property
    let g := (Langlands.Automorphic.stableAutomorphicEquiv F n).symm
      (canonicalUniformAdelicAutomorphicFormsEquiv F n hn ⟨f.val, hf⟩)
    exact ⟨g, (mem_cuspidalGeneralLinearOperatorRealization_iff F n adelicConstantTermEnveloping
      g).mpr hcuspidal⟩
  refine
    { toLinearEquiv :=
        { __ := canonicalUniformRealizationAdelicCuspidalFormMap F n hn S hS hc
          invFun := inverse
          left_inv := fun f => Subtype.ext (Subtype.ext
            ((finitePlotSmoothGeneralLinearEquiv F n).apply_symm_apply f.val.val))
          right_inv := fun f => Subtype.ext
            ((finitePlotSmoothGeneralLinearEquiv F n).symm_apply_apply f.val) }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (CompactOpen.continuous_generalLinearEquiv_symm F n).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (CompactOpen.continuous_generalLinearEquiv F n).comp
      (continuous_subtype_val.comp continuous_subtype_val)

@[simp]
theorem canonicalCuspidalRealizationAdelicEquiv_val (hn : 0 < n)
    (f : (cuspidalGeneralLinearOperatorRealization F n adelicConstantTermEnveloping).Space) :
    (canonicalCuspidalRealizationAdelicEquiv F n hn f).val =
      (finitePlotSmoothGeneralLinearEquiv F n).symm f.val.val := rfl

@[simp]
theorem canonicalCuspidalRealizationAdelicEquiv_symm_val (hn : 0 < n)
    (f : CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn) :
    ((canonicalCuspidalRealizationAdelicEquiv F n hn).symm f).val.val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

end Langlands.Automorphic.GroupSchemeFunctions
