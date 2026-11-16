import Langlands.GroupScheme.RelativeUnipotent.VectorBundleSeriesCocycle
import Langlands.GroupScheme.WeilSolvableCocycle

/-! # Weil-quotient extensions with vector-bundle series kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

open RelativeUnipotent

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {K H T : GroupScheme (Spec A)}
  (j : K ⟶ H) (q : H ⟶ T) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  [IsAffine H.X.left] [IsAffine T.X.left] [IsAffineHom K.X.hom]
  [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]
  (hK : HasFiniteVectorBundleSeries K) (e : T ≅ WeilGm.groupScheme A B)
  {U : Over (Spec A)} [Flat U.hom] [Surjective U.hom]
  [LocallyOfFinitePresentation U.hom]

include hjq hK e

/-- A finite actual vector-bundle series supplies the kernel acyclicity for
an affine extension of a supplied Picard-trivial WeilGm presentation. -/
theorem isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_pic_trivial
    [Subsingleton (CommRing.Pic B)] (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_pic_trivial j q hjq hK.cocyclesVanish e

/-- Choose one cochain on the original fppf cover for such an extension. -/
def vectorBundleWeilExtensionFppfPicardCochain
    [Subsingleton (CommRing.Pic B)] (ξ : Cocycle H U) : U ⟶ H.X :=
  Classical.choose
    (ξ.isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_pic_trivial j q hjq hK e)

/-- The chosen extension cochain satisfies its coboundary identity on all tests. -/
theorem vectorBundleWeilExtensionFppfPicardCochain_spec
    [Subsingleton (CommRing.Pic B)] (ξ : Cocycle H U)
    {Z : Over (Spec A)} (a b : Z ⟶ U) :
    ξ.toFun a b =
      (a ≫ ξ.vectorBundleWeilExtensionFppfPicardCochain j q hjq hK e) *
      (b ≫ ξ.vectorBundleWeilExtensionFppfPicardCochain j q hjq hK e)⁻¹ :=
  Classical.choose_spec
    (ξ.isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_pic_trivial j q hjq hK e) a b

/-- Finite-algebra Picard triviality gives the coefficient hypothesis. -/
theorem isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_finiteAlgebrasHaveTrivialPicard
    (hA : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} A)
    (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_finiteAlgebrasHaveTrivialPicard
    j q hjq hK.cocyclesVanish e hA

/-- The global original-cover vanishing result over a semi-local ring. -/
theorem isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_semilocal
    [Finite (MaximalSpectrum A)] (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_semilocal j q hjq hK.cocyclesVanish e

end Langlands.GroupScheme.Cocycle
