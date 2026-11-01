import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Stable freeness after localization of a module of finite projective dimension
-/

universe u v

namespace Langlands.CommutativeAlgebra

open CategoryTheory

private theorem stablyFree_right_of_free_prod
    {A K M : Type u} [CommRing A] [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [Module.Finite A K]
    [Module.IsStablyFree A K] [Module.Free A (K × M)] :
    Module.IsStablyFree A M := by
  obtain ⟨Q, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A K
  have : Module.Free A (M × (K × Q)) := Module.Free.of_equiv
    (((LinearEquiv.prodComm A K M).prodCongr (LinearEquiv.refl A Q)).trans
      (LinearEquiv.prodAssoc A M K Q))
  exact Module.IsStablyFree.of_free_prod A M (K × Q)

set_option backward.isDefEq.respectTransparency false in
/-- A projective localization of a finite module of finite projective dimension
over a Noetherian local ring is stably free. This form uses the bundled
localized module of `ModuleCat`. -/
theorem moduleCat_localizedModule_isStablyFree_of_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (S : Submonoid R) (M : ModuleCat.{u} R)
    [Module.Finite R M] [HasProjectiveDimensionLE M n]
    [Module.Projective (Localization S) (M.localizedModule S)] :
    Module.IsStablyFree (Localization S) (M.localizedModule S) := by
  induction n generalizing M with
  | zero =>
    have : CategoryTheory.Projective M :=
      (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    have : Module.Projective R M := (IsProjective.iff_projective M).mpr inferInstance
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    have : Module.Free (Localization S) (M.localizedModule S) :=
      Module.free_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
    infer_instance
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let T := f.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hP : CategoryTheory.Projective T.X₂ := inferInstance
    have : HasProjectiveDimensionLE T.X₁ n :=
      (hT.hasProjectiveDimensionLT_X₃_iff n hP).mp inferInstance
    let TS := T.map (ModuleCat.localizedModuleFunctor S)
    have hTS : TS.ShortExact :=
      hT.map_of_exact (ModuleCat.localizedModuleFunctor S)
    have : IsLocalizedModule S (T.X₂.localizedModuleMkLinearMap S) :=
      ModuleCat.localizedModule_isLocalizedModule T.X₂ S
    have : Module.Free (Localization S) (T.X₂.localizedModule S) :=
      Module.free_of_isLocalizedModule S (T.X₂.localizedModuleMkLinearMap S)
    have : CategoryTheory.Projective TS.X₃ :=
      ModuleCat.projective_of_categoryTheory_projective (M.localizedModule S)
    let e : (T.X₂.localizedModule S) ≃ₗ[Localization S]
        ((T.X₁.localizedModule S) × (M.localizedModule S)) :=
      (hTS.splittingOfProjective.isoBinaryBiproduct ≪≫
        ModuleCat.biprodIsoProd TS.X₁ TS.X₃).toLinearEquiv
    have : Module.Free (Localization S)
        ((T.X₁.localizedModule S) × (M.localizedModule S)) :=
      Module.Free.of_equiv e
    have : Module.Projective (Localization S)
        ((T.X₁.localizedModule S) × (M.localizedModule S)) :=
      Module.Projective.of_free
    have : Module.Projective (Localization S) (T.X₁.localizedModule S) :=
      Module.Projective.of_split
        (LinearMap.inl (Localization S) (T.X₁.localizedModule S) (M.localizedModule S))
        (LinearMap.fst (Localization S) (T.X₁.localizedModule S) (M.localizedModule S))
        (by ext; rfl)
    have : Module.IsStablyFree (Localization S) (T.X₁.localizedModule S) := ih T.X₁
    have : IsLocalizedModule S (T.X₁.localizedModuleMkLinearMap S) :=
      ModuleCat.localizedModule_isLocalizedModule T.X₁ S
    have : Module.Finite (Localization S) (T.X₁.localizedModule S) :=
      Module.Finite.of_isLocalizedModule S (T.X₁.localizedModuleMkLinearMap S)
    exact stablyFree_right_of_free_prod (A := Localization S) (K := T.X₁.localizedModule S)

/-- A version for any model of the localized module over `Localization S`. -/
theorem isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] (S : Submonoid R)
    {N : Type v} [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N] (f : M →ₗ[R] N) [IsLocalizedModule S f]
    [Module.Projective (Localization S) N] :
    Module.IsStablyFree (Localization S) N := by
  let B := ModuleCat.of R M
  have : IsLocalizedModule S (B.localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule B S
  let e : (B.localizedModule S) ≃ₗ[Localization S] N :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S (B.localizedModuleMkLinearMap S) f)
  have : Module.Projective (Localization S) (B.localizedModule S) :=
    Module.Projective.of_equiv e.symm
  have : Module.IsStablyFree (Localization S) (B.localizedModule S) :=
    moduleCat_localizedModule_isStablyFree_of_hasProjectiveDimensionLE n S B
  exact Module.IsStablyFree.equiv e

/-- Canonical localized modules of finite projective dimension are stably free
whenever they are projective. -/
theorem localizedModule_isStablyFree_of_hasProjectiveDimensionLE
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] (S : Submonoid R)
    [Module.Projective (Localization S) (LocalizedModule S M)] :
    Module.IsStablyFree (Localization S) (LocalizedModule S M) :=
  isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE n S
    (LocalizedModule.mkLinearMap S M)

/-- An invertible localization of a finite module of finite projective dimension
over a Noetherian local ring is free. -/
theorem localizedModule_free_of_invertible_of_hasProjectiveDimensionLE
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] (S : Submonoid R)
    [Module.Invertible (Localization S) (LocalizedModule S M)] :
    Module.Free (Localization S) (LocalizedModule S M) := by
  have : Module.IsStablyFree (Localization S) (LocalizedModule S M) :=
    localizedModule_isStablyFree_of_hasProjectiveDimensionLE n S
  exact Module.free_of_isStablyFree_of_invertible (Localization S) (LocalizedModule S M)

end Langlands.CommutativeAlgebra
