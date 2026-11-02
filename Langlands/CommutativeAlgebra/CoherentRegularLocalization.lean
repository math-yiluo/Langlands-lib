import Langlands.CommutativeAlgebra.ValuationFiniteFreePresentation
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! # Localization of coherence and finite projective dimension -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- The finite-free-submodule coherence condition together with finite
projective dimension for every finitely presented module. -/
def FinitelyPresentedRegularRing (R : Type u) [CommRing R] : Prop :=
  FiniteFreeSubmoduleCoherent R ∧
    FiniteProjectiveDimensionForFinitelyPresentedModules R

/-- The finite-free-submodule coherence condition passes to every
localization algebra, with an independent universe for that algebra. -/
theorem finiteFreeSubmoduleCoherent_of_isLocalization
    {R : Type u} [CommRing R] (hcoh : FiniteFreeSubmoduleCoherent R)
    (S : Submonoid R) (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalization S A] :
    FiniteFreeSubmoduleCoherent A := by
  intro n P hP
  let f : (Fin n → R) →ₗ[R] (Fin n → A) :=
    LinearMap.pi fun i ↦ (Algebra.linearMap R A) ∘ₗ LinearMap.proj i
  have : IsLocalizedModule S f :=
    IsLocalizedModule.pi S (fun _ : Fin n ↦ Algebra.linearMap R A)
  obtain ⟨K, hK, hKP⟩ := exists_fg_submodule_localized'_eq S f P hP
  have : Module.FinitePresentation R K := hcoh n K hK
  have : Module.FinitePresentation A (K.localized' A S f) :=
    Module.FinitePresentation.of_equiv
      (IsLocalizedModule.isBaseChange S A (K.toLocalized' A S f)).equiv
  exact Module.FinitePresentation.of_equiv (LinearEquiv.ofEq _ _ hKP)

/-- An actual localized-module model inherits a projective-dimension
bound from the module before localization. -/
theorem hasProjectiveDimensionLE_of_isLocalizedModule
    {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (n : ℕ) [CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of (Localization S) N) n := by
  let B := ModuleCat.of R M
  have : CategoryTheory.HasProjectiveDimensionLE (B.localizedModule S) n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n S B
  have : IsLocalizedModule S (B.localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule B S
  let e : (B.localizedModule S) ≃ₗ[Localization S] N :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S (B.localizedModuleMkLinearMap S) f)
  exact CategoryTheory.hasProjectiveDimensionLT_of_iso e.toModuleIso (n + 1)

/-- Finite projective dimension for finitely presented modules passes to
every localization, without a coherence assumption. -/
theorem finiteProjectiveDimensionForFinitelyPresentedModules_localization
    {R : Type u} [CommRing R]
    (hPD : FiniteProjectiveDimensionForFinitelyPresentedModules R)
    (S : Submonoid R) :
    FiniteProjectiveDimensionForFinitelyPresentedModules (Localization S) := by
  intro N _ _ _
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let d := finitelyPresentedLocalizationModel S N
  obtain ⟨n, hn⟩ := hPD d.Carrier
  let : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R d.Carrier) n := hn
  exact ⟨n, hasProjectiveDimensionLE_of_isLocalizedModule S d.localizationMap n⟩

/-- Both conditions in `FinitelyPresentedRegularRing` pass to a
localization. -/
theorem finitelyPresentedRegularRing_localization
    {R : Type u} [CommRing R] (hR : FinitelyPresentedRegularRing R)
    (S : Submonoid R) :
    FinitelyPresentedRegularRing (Localization S) :=
  ⟨finiteFreeSubmoduleCoherent_of_isLocalization hR.1 S (Localization S),
    finiteProjectiveDimensionForFinitelyPresentedModules_localization hR.2 S⟩

/-- Every arbitrary-rank valuation domain satisfies the two conditions. -/
theorem finitelyPresentedRegularRing_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] :
    FinitelyPresentedRegularRing R :=
  ⟨finiteFreeSubmoduleCoherent_of_valuationRing R,
    finiteProjectiveDimensionForFinitelyPresentedModules_of_valuationRing R⟩

/-- All localizations of arbitrary valuation domains satisfy the two
conditions, including localizations in which zero is inverted. -/
theorem finitelyPresentedRegularRing_localization_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (S : Submonoid R) :
    FinitelyPresentedRegularRing (Localization S) :=
  finitelyPresentedRegularRing_localization (finitelyPresentedRegularRing_of_valuationRing R) S

/-- The projective-dimension bound at most one remains valid over every
localization of an arbitrary valuation domain. -/
theorem hasProjectiveDimensionLE_one_of_finitePresentation_of_valuationRing_localization
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (S : Submonoid R)
    (N : Type u) [AddCommGroup N] [Module (Localization S) N]
    [Module.FinitePresentation (Localization S) N] :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of (Localization S) N) 1 := by
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let d := finitelyPresentedLocalizationModel S N
  have : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R d.Carrier) 1 :=
    hasProjectiveDimensionLE_one_of_finitePresentation_of_valuationRing d.Carrier
  exact hasProjectiveDimensionLE_of_isLocalizedModule S d.localizationMap 1

end Langlands.CommutativeAlgebra
