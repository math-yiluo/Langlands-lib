import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.Rational.DynamicLeviCocharacterRealizationStatement

/-! # Assembly of simultaneous dynamic Levi realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A cocharacter of a represented dynamic Levi admits simultaneous ambient
parabolic, centralizer and unipotent realization on every test scheme. -/
theorem dynamicLeviCocharacterRealization :
    DynamicLeviCocharacterRealizationStatement.{u} := by
  intro k _ G hG χ L j hjc hj ν
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have htau := Dynamic.range_comp_le_centralizer χ j hj ν
  obtain ⟨N, hN⟩ := Dynamic.exists_dominant_inclusions χ (ν ≫ j) htau
  let ψ := Dynamic.cocharacterCombination χ (ν ≫ j) htau (N : ℤ)
  have hformula : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ ψ.hom.hom = ((t ^ (N : ℤ)) ≫ χ.hom.hom) * (t ≫ (ν ≫ j).hom.hom) := by
    intro T t
    exact Dynamic.comp_cocharacterCombination χ (ν ≫ j) htau (N : ℤ) t
  obtain ⟨hP, hU, hZ⟩ := hN (N : ℤ) le_rfl ψ hformula
  refine ⟨ψ, ?_⟩
  exact Dynamic.realization_cocharacterCombination_of_inclusions χ j hj hjc ν (N : ℤ)
    hP hU hZ

end Langlands.GroupScheme
