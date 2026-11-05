import Langlands.Geometry.Building.CentralIsogenyTranslation
import Langlands.GroupScheme.Rational.TorusCoverNormalizer
import Langlands.GroupScheme.Rational.SplitTorusFppfImage

/-! # Actual normalizer derivatives in a central-isogeny square -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono j.hom.hom.left]
  (q : C ⟶ G) (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

/-- The actual ambient point map on normalizers for an isogeny of supplied split tori. -/
def splitTorusIsogenyNormalizerMap : normalizerPoints i →* normalizerPoints j := by
  letI : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  letI : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  letI : LocallyOfFinitePresentation (CommGroupScheme.groupHom t).hom.hom.left :=
    locallyOfFinitePresentation_of_splitTori hS hT t
  exact TorusCoverTransport.normalizerPointsMap q t h

@[simp] theorem splitTorusIsogenyNormalizerMap_coe (n : normalizerPoints i) :
    (splitTorusIsogenyNormalizerMap q hS hT t h ht n : rationalPoints G) =
      rationalPoints.map q n.val := rfl

/-- The original torus map commutes with the actual normalizer automorphisms. -/
theorem normalizingAut_splitTorusIsogenyNormalizerMap (n : normalizerPoints i) :
    (normalizingAut i n).hom ≫ t =
      t ≫ (normalizingAut j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)).hom := by
  let : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  let : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  let : LocallyOfFinitePresentation (CommGroupScheme.groupHom t).hom.hom.left :=
    locallyOfFinitePresentation_of_splitTori hS hT t
  exact TorusCoverTransport.normalizingAut_comp q t h n

variable [Mono i.hom.hom.left]

/-- Actual cocharacter postcomposition intertwines the actual image-normalizer action. -/
theorem cocharacterMapReal_splitTorusIsogenyNormalizerMap
    (n : normalizerPoints i) (v : V S) :
    cocharacterMapReal t (normalizerAction i n v) =
      normalizerAction j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)
        (cocharacterMapReal t v) := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [normalizerAction_tmul, cocharacterMapReal_tmul,
      Category.assoc, normalizingAut_splitTorusIsogenyNormalizerMap q hS hT t h ht n]
  | add v w hv hw => simp only [map_add, hv, hw]

variable [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  (hq : IsCentralIsogeny q)

/-- The actual reduced translation equivalence intertwines both actual derivatives. -/
theorem centralIsogenyTranslationEquiv_translationAction (n : normalizerPoints i)
    (v : TranslationSpace i) :
    centralIsogenyTranslationEquiv q hq hS hT t h ht (translationAction i n v) =
      translationAction j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)
        (centralIsogenyTranslationEquiv q hq hS hT t h ht v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationAction_mk, centralIsogenyTranslationEquiv_mk,
    centralIsogenyTranslationEquiv_mk, translationAction_mk]
  exact congrArg Submodule.Quotient.mk
    (cocharacterMapReal_splitTorusIsogenyNormalizerMap q hS hT t h ht n w)

end Langlands.Geometry.Building
