import Langlands.GroupScheme.AffineHomImageHopfAdapter
import Langlands.GroupScheme.AffineHomImageStatement
import Langlands.GroupScheme.AffineKernelQuotient

/-! # Reduction of the actual fppf image theorem to Hopf-subalgebra flatness -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Hopf-subalgebra faithful flatness over every field proves the exact actual
fppf homomorphism-image statement, including nonsmooth groups and full kernels. -/
theorem affineHomImage_of_hopfSubalgebraFaithfullyFlat
    (hff : ∀ (k : Type u) [Field k],
      AffineHomImageHopfAdapter.HopfSubalgebraFaithfullyFlatStatement k) :
    AffineHomImageStatement.{u} := by
  intro k _ G H _ _ _ _ f
  obtain ⟨hflat, hsurj⟩ :=
    AffineHomImageHopfAdapter.flat_and_surjective (hff k) (AffineHomImage.projection f)
  have : LocallyOfFiniteType (AffineHomImage.projection f).hom.hom.left := by
    have : LocallyOfFiniteType
        ((AffineHomImage.projection f).hom.hom.left ≫ (AffineHomImage.image f).X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (AffineHomImage.image f).X.hom
  have : IsLocallyNoetherian (AffineHomImage.image f).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (AffineHomImage.image f).X.hom
  exact ⟨AffineHomImage.image f, AffineHomImage.projection f, AffineHomImage.inclusion f,
    inferInstance, inferInstance,
    (inferInstance : IsClosedImmersion (AffineHomImage.inclusion f).hom.hom.left),
    AffineHomImage.projection_inclusion f,
    hflat, hsurj, inferInstance, AffineHomImage.kernel_range_projection f⟩

end Langlands.GroupScheme
