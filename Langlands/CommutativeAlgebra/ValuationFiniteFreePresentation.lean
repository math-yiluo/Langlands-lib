import Langlands.CommutativeAlgebra.CoherentLocalizationPicard
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite free presentations over arbitrary valuation domains -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- A finite free surjection onto a module together with a finite free
description of its actual kernel. -/
structure FiniteFreeKernelPresentation
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] where
  generators : ℕ
  quotientMap : (Fin generators → R) →ₗ[R] M
  quotientMap_surjective : Function.Surjective quotientMap
  relations : ℕ
  kernelEquiv : (Fin relations → R) ≃ₗ[R] LinearMap.ker quotientMap

/-- Torsion-free modules over a valuation domain are flat. -/
theorem flat_of_isTorsionFree_of_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Module.Flat R M := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- A finitely generated torsion-free module over an arbitrary valuation
domain is free. -/
theorem free_of_finite_of_isTorsionFree_of_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] :
    Module.Free R M := by
  have : Module.Flat R M := flat_of_isTorsionFree_of_valuationRing M
  exact Module.free_of_flat_of_isLocalRing

/-- Valuation domains satisfy the finite-free-submodule coherence
condition, with no rank or Noetherian restriction. -/
theorem finiteFreeSubmoduleCoherent_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] :
    FiniteFreeSubmoduleCoherent R := by
  intro n K hK
  let : Module.Finite R K := Module.Finite.of_fg hK
  have : Module.Free R K := free_of_finite_of_isTorsionFree_of_valuationRing K
  exact Module.finitePresentation_of_projective R K

/-- Every finitely presented module over a valuation domain has a finite
free surjection with finite free kernel. -/
theorem nonempty_finiteFreeKernelPresentation_of_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    Nonempty (FiniteFreeKernelPresentation R M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  have : Module.Free R (LinearMap.ker f) :=
    free_of_finite_of_isTorsionFree_of_valuationRing (LinearMap.ker f)
  exact ⟨{
    generators := n
    quotientMap := f
    quotientMap_surjective := hf
    relations := Module.finrank R (LinearMap.ker f)
    kernelEquiv := (Module.finBasis R (LinearMap.ker f)).equivFun.symm
  }⟩

/-- A chosen finite free surjection and finite free kernel for a finitely
presented module over a valuation domain. -/
noncomputable def valuationRingFiniteFreeKernelPresentation
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    FiniteFreeKernelPresentation R M :=
  Classical.choice (nonempty_finiteFreeKernelPresentation_of_valuationRing M)

/-- Finitely presented modules over arbitrary valuation domains have
projective dimension at most one. -/
theorem hasProjectiveDimensionLE_one_of_finitePresentation_of_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) 1 := by
  let d := valuationRingFiniteFreeKernelPresentation (R := R) M
  have : Module.Free R (LinearMap.ker d.quotientMap) :=
    Module.Free.of_equiv d.kernelEquiv
  have hK : CategoryTheory.HasProjectiveDimensionLT
      (ModuleCat.of R (LinearMap.ker d.quotientMap)) 1 := inferInstance
  have hF : CategoryTheory.HasProjectiveDimensionLT
      (ModuleCat.of R (Fin d.generators → R)) 2 :=
    CategoryTheory.hasProjectiveDimensionLT_of_ge _ 1 2 (by omega)
  exact (LinearMap.shortExact_shortComplexKer d.quotientMap_surjective).hasProjectiveDimensionLT_X₃
    1 hK hF

/-- The finite-projective-dimension condition for finitely presented
modules holds for all valuation domains. -/
theorem finiteProjectiveDimensionForFinitelyPresentedModules_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] :
    FiniteProjectiveDimensionForFinitelyPresentedModules R := by
  intro M _ _ _
  exact ⟨1, hasProjectiveDimensionLE_one_of_finitePresentation_of_valuationRing M⟩

end Langlands.CommutativeAlgebra
