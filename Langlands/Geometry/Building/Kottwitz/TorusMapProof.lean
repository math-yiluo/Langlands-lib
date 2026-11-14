import Langlands.Geometry.Building.Kottwitz.TorusKottwitzTransfer
import Langlands.Geometry.Building.Kottwitz.TorusSplittingField

/-! # Proof of existence, uniqueness and splitting-field independence of the torus Kottwitz map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

/-- KP Proposition 11.1.1: the torus Kottwitz homomorphism exists, is unique, is onto, and
is characterized by the norm square at every finite Galois splitting field. -/
theorem torusKottwitzExistence : TorusKottwitzExistenceStatement.{u} := by
  intro F _ _ _ _ k _ _ _ _ _ T hT
  let : IsAffine T.X.left := torusIsAffine k T hT
  obtain ⟨L₀, _, _, hL₀⟩ := exists_finiteGalois_splitting F k T hT
  obtain ⟨κ₀, hκ₀⟩ := exists_torusNormLawAt F k T L₀ hL₀
  have hκ₀' : IsTorusKottwitzHom F k T κ₀ := fun L _ _ hL =>
    torusNormLawAt_of_torusNormLawAt F k T L₀ L hL₀ hL hκ₀
  have hspec : IsTorusKottwitzHom F k T (torusKottwitz F k T hT) :=
    torusKottwitz_spec F k T hT ⟨κ₀, hκ₀'⟩
  have heq : torusKottwitz F k T hT = κ₀ :=
    eq_of_torusNormLawAt F k T L₀ hL₀ (hspec L₀ hL₀) hκ₀
  refine ⟨⟨κ₀, hκ₀', fun κ hκ => eq_of_torusNormLawAt F k T L₀ hL₀ (hκ L₀ hL₀) hκ₀⟩,
    hspec, ?_, ?_⟩
  · exact surjective_of_torusNormLawAt F k T L₀ hL₀ (heq ▸ hκ₀)
  · intro L _ _ hL
    refine ⟨relativeNorm_unramifiedClosure_surjective F k T L hL, fun κ => ⟨fun hκ => ?_, ?_⟩⟩
    · exact eq_of_torusNormLawAt F k T L hL hκ (hspec L hL)
    · rintro rfl
      exact hspec L hL

end Langlands.Geometry.Building.Kottwitz
