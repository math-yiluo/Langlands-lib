import Langlands.GroupScheme.Torus.SplitAdicSpecialHom
import Langlands.GroupScheme.Torus.CompleteLocalDeformation.CoverDescent
import Langlands.GroupScheme.Torus.CompleteLocalSpecialIsoImmersion
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationStatement

/-! # Homomorphisms into complete-local deformations of multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Homomorphisms into a flat affine deformation of a multiplicative-type group
are determined by their special fibres; a special-fibre isomorphism from a
finite-etale-split source is an open and closed immersion. -/
theorem multiplicativeTypeCompleteLocalDeformation :
    MultiplicativeTypeCompleteLocalDeformationStatement.{u} := by
  intro A _ _ _ _ G H _ _ _ hH
  dsimp only
  intro hG
  let d := simultaneousSplitting A G H hH hG
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hbij := specialFibre_hom_bijective_of_splitCover d.source d.targetSpecial
    (fun f₀ fB hfB => exists_descent_of_specialHomTransport
      d.source d.targetSpecial f₀ fB hfB)
  constructor
  · intro f₀
    obtain ⟨f, hf⟩ := hbij.surjective f₀
    exact ⟨f, hf, fun g hg => hbij.injective (hg.trans hf.symm)⟩
  · intro f hf
    let : IsIso ((GroupScheme.baseChange
      (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := hf
    exact open_and_closed_of_special_isIso_of_finiteEtaleSplit hH f

end Langlands.GroupScheme
