import Langlands.CommutativeAlgebra.RegularLocalLocalizationsStatement
import Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionProof
import Langlands.CommutativeAlgebra.ResidueFieldFiniteProjectiveDimensionRegularProof
import Langlands.CommutativeAlgebra.FiniteModuleLocalizationDescent
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-! # Prime localizations of regular local rings are regular -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory

/-- Finite projective dimension for finite modules passes to a localization. -/
theorem finiteProjectiveDimension_localization
    {R : Type u} [CommRing R]
    (hPD : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n)
    (S : Submonoid R) (N : Type u) [AddCommGroup N]
    [Module (Localization S) N] [Module.Finite (Localization S) N] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of (Localization S) N) n := by
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨K, hK, hloc⟩ := exists_fg_submodule_isLocalizedModule (N := N) S
  let : Module.Finite R K := Module.Finite.of_fg hK
  let : IsLocalizedModule S K.subtype := hloc
  obtain ⟨n, hn⟩ := hPD K
  let : HasProjectiveDimensionLE (ModuleCat.of R K) n := hn
  let B := ModuleCat.of R K
  have : HasProjectiveDimensionLE (B.localizedModule S) n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n S B
  have : IsLocalizedModule S (B.localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule B S
  let e : (B.localizedModule S) ≃ₗ[Localization S] N :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S (B.localizedModuleMkLinearMap S) K.subtype)
  exact ⟨n, hasProjectiveDimensionLT_of_iso e.toModuleIso (n + 1)⟩

/-- The two homological criteria imply regularity at every prime. -/
theorem regularLocalLocalizations_of_homologicalCriteria
    (hPD : RegularLocalFiniteProjectiveDimensionStatement.{u})
    (hReg : ResidueFieldFiniteProjectiveDimensionRegularStatement.{u}) :
    RegularLocalLocalizationsStatement.{u} := by
  intro R _ hR
  let : IsRegularLocalRing R := hR
  apply isRegularRing_iff.mpr
  intro p _
  apply hReg (Localization.AtPrime p)
  exact finiteProjectiveDimension_localization (hPD R hR) p.primeCompl
    (IsLocalRing.ResidueField (Localization.AtPrime p))

/-- The published forward theorem reduces localization regularity to the residue criterion. -/
theorem regularLocalLocalizations_of_residueCriterion
    (hReg : ResidueFieldFiniteProjectiveDimensionRegularStatement.{u}) :
    RegularLocalLocalizationsStatement.{u} :=
  regularLocalLocalizations_of_homologicalCriteria
    regularLocalFiniteProjectiveDimension hReg

/-- Every prime localization of a regular local ring is regular. -/
theorem regularLocalLocalizations : RegularLocalLocalizationsStatement.{u} :=
  regularLocalLocalizations_of_residueCriterion
    residueFieldFiniteProjectiveDimensionRegular

end Langlands.CommutativeAlgebra
