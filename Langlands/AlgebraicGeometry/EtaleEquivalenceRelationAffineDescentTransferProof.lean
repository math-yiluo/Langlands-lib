import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentTransferStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation

/-! # Transfer of finite-surjective affine descent to algebraic spaces

Finite-surjective descent of affineness for étale equivalence relations implies Stacks
Project Lemma 70.15.1 (Tag 07VS) for algebraic spaces over a base scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace EtaleEquivalenceRelation

/-- Finite-surjective descent of affineness for étale equivalence relations implies
finite-surjective descent of affineness for algebraic spaces. -/
theorem etaleEquivalenceRelationAffineDescentTransfer :
    EtaleEquivalenceRelationAffineDescentTransferStatement.{u} := by
  intro hG S X Y f hfin hsurj ⟨V, hV, ⟨e⟩⟩
  let c : (schemeYoneda S).obj V ⟶ Y.presheaf := e.hom ≫ hom f
  have hc : AlgebraicSpace.IsFinite c :=
    MorphismProperty.RespectsIso.precomp ((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u}) (Over.forget S)).relative (schemeYoneda S))
      e.hom (hom f) hfin
  have hcs : AlgebraicSpace.IsSurjective c :=
    MorphismProperty.RespectsIso.precomp ((MorphismProperty.inverseImage
      (@Surjective.{u}) (Over.forget S)).relative (schemeYoneda S)) e.hom (hom f) hsurj
  obtain ⟨U, a, -, ha, has⟩ := Y.exists_atlas
  obtain ⟨U₀, a₀, hU₀, he, hes⟩ := exists_affine_atlas a ha has c hcs
  obtain ⟨R, t, s, h, ht, hs⟩ := exists_kernelPair he
  have hcov := ofKernelPair_hasFiniteSurjectiveCoverWithAffineQuotient h ht hs he hes c hc hcs
  exact exists_isAffine_iso_of_hasAffineQuotient (Y := Y.toSheaf) h ht hs he hes
    (hG _ hU₀ hcov)

end Langlands.AlgebraicGeometry
