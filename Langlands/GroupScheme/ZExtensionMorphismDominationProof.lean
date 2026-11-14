import Langlands.GroupScheme.ZExtensionPullbackGeometry
import Langlands.GroupScheme.Torus.InducedProducts
import Langlands.GroupScheme.Reductive.TorusKernelAscent
import Langlands.GroupScheme.ZExtensionCentralSurjectionProof

/-! # Morphism-compatible domination of actual z-extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

open ZExtensionPullback

/-- KP Lemma 11.4.3 for the actual supplied source and target extensions. -/
theorem zExtensionMorphismDomination : ZExtensionMorphismDominationStatement.{u} := by
  intro k _ G H hG _ z t f
  have hInduced : IsInducedTorus (kernelGroup z t) :=
    IsInducedTorus.of_product_iso (Iso.refl _)
      z.isZExtension.induced t.isZExtension.induced
  have : IsAffineHom (group z t f).X.hom := affine z t f
  have hReductive : IsConnectedReductive (group z t f) :=
    IsConnectedReductive.of_torusKernel
      (inclusion z t f) (inclusion_closed z t f) hInduced.isTorus
      (quotient z t f) hG
  have : Surjective (first z t f).hom.hom.left := (first_fppf z t f).2.1
  have hDerived : HasSimplyConnectedDerivedGroup (group z t f) :=
    HasSimplyConnectedDerivedGroup.of_centralSurjection
      hReductive z.isZExtension.source_reductive (first z t f)
      (first_kernel_central z t f) z.isZExtension.derived_simplyConnected
  let w : ZExtension G :=
    { Z := kernelGroup z t
      H := group z t f
      i := inclusion z t f
      p := projection z t f
      isZExtension :=
        { induced := hInduced
          closed := inclusion_closed z t f
          central := inclusion_central z t f
          quotient := quotient z t f
          source_reductive := hReductive
          target_reductive := hG
          derived_simplyConnected := hDerived } }
  exact ⟨w, first z t f, second z t f, rfl, second_comp z t f⟩

end Langlands.GroupScheme
