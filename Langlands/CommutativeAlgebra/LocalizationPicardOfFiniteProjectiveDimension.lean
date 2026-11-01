import Langlands.CommutativeAlgebra.FiniteModuleLocalizationDescent
import Langlands.CommutativeAlgebra.FiniteProjectiveDimensionLocalization
import Mathlib.RingTheory.PicardGroup

/-! # Conditional Picard vanishing for localizations of a local ring -/

universe u

namespace Langlands.CommutativeAlgebra

/-- If all finite modules over a Noetherian local ring have finite projective
dimension, the Picard group of every localization is trivial. -/
theorem subsingleton_pic_localization_of_finite_projectiveDimension
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hPD : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n)
    (S : Submonoid R) :
    Subsingleton (CommRing.Pic (Localization S)) := by
  apply CommRing.Pic.subsingleton_iff.mpr
  intro N _ _ hN
  let : Module.Invertible (Localization S) N := hN
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  obtain ⟨K, hK, hloc⟩ := exists_fg_submodule_isLocalizedModule (N := N) S
  let : Module.Finite R K := Module.Finite.of_fg hK
  let : IsLocalizedModule S K.subtype := hloc
  obtain ⟨n, hn⟩ := hPD K
  let : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R K) n := hn
  have : Module.IsStablyFree (Localization S) N :=
    isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE n S K.subtype
  exact Module.free_of_isStablyFree_of_invertible (Localization S) N

end Langlands.CommutativeAlgebra
