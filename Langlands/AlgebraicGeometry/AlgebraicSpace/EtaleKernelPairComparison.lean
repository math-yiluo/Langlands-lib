import Langlands.AlgebraicGeometry.AlgebraicSpace.CommonRepresentedKernelPair
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The compatible isomorphism between etale sheaves with locally surjective
presentations having the same represented kernel pair. -/
def commonEtaleKernelPairIso
    {F G : Presheaf S} {R U : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hG : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) G)
    (t s : R ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj U ⟶ G)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hA : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hB : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b) :
    F ≅ G :=
  commonEtalePresentationIso hF hG a b ha hb
    (same_kernel_of_common_represented_kernelPair t s a b hA hB)

/-- The common-kernel-pair isomorphism identifies the presentation maps. -/
theorem commonEtaleKernelPairIso_hom_fac
    {F G : Presheaf S} {R U : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hG : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) G)
    (t s : R ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj U ⟶ G)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hA : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hB : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b) :
    a ≫ (commonEtaleKernelPairIso hF hG t s a b ha hb hA hB).hom = b :=
  commonEtalePresentationIso_hom_fac hF hG a b ha hb
    (same_kernel_of_common_represented_kernelPair t s a b hA hB)

/-- An etale sheaf is an fppf sheaf if an fppf sheaf has an etale-local
presentation with the same represented kernel pair. -/
theorem isSheaf_fppf_of_common_etale_kernelPair
    {F : Presheaf S} {G : FppfSheaf S} {R U : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (t s : R ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj U ⟶ G.obj)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hA : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hB : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F :=
  isSheaf_fppf_of_common_etale_presentation hF a b ha hb
    (same_kernel_of_common_represented_kernelPair t s a b hA hB)

end Langlands.AlgebraicGeometry.AlgebraicSpace
