import Langlands.CommutativeAlgebra.FinitelyPresentedLocalizationDescent
import Langlands.CommutativeAlgebra.FinitelyPresentedProjectiveDimensionLocalization
import Mathlib.RingTheory.PicardGroup

/-! # Conditional Picard vanishing for coherent local rings -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- Every finitely presented module over `R`, in the universe of `R`, has
some finite bound on its projective dimension. -/
def FiniteProjectiveDimensionForFinitelyPresentedModules
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M],
    ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n

/-- Every invertible module over a localization of a coherent local ring
is free if every finitely presented module over the ring has finite
projective dimension. -/
theorem free_invertible_localization_of_finitelyPresented_finite_projectiveDimension
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hcoh : FiniteFreeSubmoduleCoherent R)
    (hPD : FiniteProjectiveDimensionForFinitelyPresentedModules R)
    (S : Submonoid R)
    (N : Type v) [AddCommGroup N] [Module (Localization S) N]
    [Module.Invertible (Localization S) N] :
    Module.Free (Localization S) N := by
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N :=
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  have : Module.FinitePresentation (Localization S) N :=
    Module.finitePresentation_of_projective (Localization S) N
  let d := finitelyPresentedLocalizationModel S N
  obtain ⟨n, hn⟩ := hPD d.Carrier
  let : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R d.Carrier) n := hn
  have : Module.IsStablyFree (Localization S) N :=
    isStablyFree_of_isLocalizedModule_of_finitePresentation hcoh n S d.localizationMap
  exact Module.free_of_isStablyFree_of_invertible (Localization S) N

/-- Under the displayed coherence and finite-projective-dimension
conditions, every localization of a local ring has trivial Picard group. -/
theorem subsingleton_pic_localization_of_finitelyPresented_finite_projectiveDimension
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hcoh : FiniteFreeSubmoduleCoherent R)
    (hPD : FiniteProjectiveDimensionForFinitelyPresentedModules R)
    (S : Submonoid R) :
    Subsingleton (CommRing.Pic (Localization S)) := by
  apply CommRing.Pic.subsingleton_iff.mpr
  intro N _ _ hN
  let : Module.Invertible (Localization S) N := hN
  exact free_invertible_localization_of_finitelyPresented_finite_projectiveDimension
    hcoh hPD S N

end Langlands.CommutativeAlgebra
