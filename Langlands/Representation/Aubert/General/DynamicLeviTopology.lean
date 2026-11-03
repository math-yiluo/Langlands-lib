import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.Representation.Category.Contragredient

/-! # Point topology and compact-open cofinality for actual dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- The actual affine dynamic-centralizer model has the same multiplicative
point topology as its subgroup of the ambient identity-test points. -/
def dynamicCentralizerPointHomeomorph
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G) :
    have : IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
      Dynamic.Affine.isClosedSubgroup_centralizerHom χ
    have : IsAffine (Dynamic.Affine.centralizerScheme χ).X.left :=
      isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    let : TopologicalSpace (RationalPoint R (Dynamic.Affine.centralizerScheme χ).X) :=
      rationalPointTopology R (Dynamic.Affine.centralizerScheme χ).X
    RationalPoint R (Dynamic.Affine.centralizerScheme χ).X ≃ₜ*
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) := by
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have : IsAffine (Dynamic.Affine.centralizerScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : TopologicalSpace (RationalPoint R (Dynamic.Affine.centralizerScheme χ).X) :=
    rationalPointTopology R (Dynamic.Affine.centralizerScheme χ).X
  exact rationalPointSubgroupHomeomorph R (Dynamic.centralizer χ)
    (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)

@[simp] theorem dynamicCentralizerPointHomeomorph_apply_coe
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    (p : RationalPoint R (Dynamic.Affine.centralizerScheme χ).X) :
    (dynamicCentralizerPointHomeomorph R G χ p : RationalPoint R G.X) =
      p ≫ (Dynamic.Affine.centralizerHom χ).hom.hom := rfl

/-- The actual dynamic centralizer has compact open subgroups cofinal among
its open subgroups, with the subspace topology from the pinned point topology. -/
theorem dynamicCentralizer_compactOpenCofinal
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [IsTopologicalGroup (RationalPoint F G.X)],
      CompactOpenCofinal
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
          Subgroup (RationalPoint F G.X)) := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  change ∀ [IsTopologicalGroup (RationalPoint F G.X)],
    CompactOpenCofinal
      ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Subgroup (RationalPoint F G.X))
  intro _
  exact represented_rationalPoint_subgroup_compactOpenCofinal F G
    (Dynamic.centralizer χ) (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)

end Langlands.Aubert.General
