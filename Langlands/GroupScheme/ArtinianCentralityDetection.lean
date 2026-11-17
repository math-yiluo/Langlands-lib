import Langlands.AlgebraicGeometry.Deformation.ArtinianGeneralSchemeDetection
import Langlands.GroupScheme.Reductive.ArtinianCentrality

/-! # Artinian detection of centrality with arbitrary ambient group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ArtinianCentrality

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Local Artinian base changes detect centrality when the universal product is
locally noetherian, without an affineness condition on the ambient group. -/
theorem isCentral_of_artinian_baseChange_general (i : H ⟶ G)
    [IsLocallyNoetherian (H.X ⊗ G.X).left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) : IsCentral i := by
  apply isCentral_of_universal_commute i
  apply Over.OverMorphism.ext
  apply Langlands.AlgebraicGeometry.Deformation.ArtinianDetection.hom_ext_general
  intro A _ _ _ t
  let b : Spec (CommRingCat.of A) ⟶ S := t ≫ (H.X ⊗ G.X).hom
  let V : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let q : (Over.map b).obj V ⟶ H.X ⊗ G.X :=
    Over.homMk t (by simp [V, b])
  let x := (baseChangePointsEquiv b H V).symm (q ≫ fst H.X G.X)
  let y := (baseChangePointsEquiv b G V).symm (q ≫ snd H.X G.X)
  have he := congrArg (baseChangePointsEquiv b G V)
    (commute_of_mem_center (hc A b V x) y).eq
  have hq : q ≫ ((fst H.X G.X ≫ i.hom.hom) * snd H.X G.X) =
      q ≫ (snd H.X G.X * (fst H.X G.X ≫ i.hom.hom)) := by
    simpa only [map_mul, baseChangePointsEquiv_comp, x, y, MulEquiv.apply_symm_apply,
      MonObj.comp_mul, Category.assoc] using he
  exact congrArg CommaMorphism.left hq

/-- The unchanged monomorphic source, bundled as commutative using centrality
on every local Artinian base change, with arbitrary ambient group scheme. -/
def commGroupSchemeOfArtinianCentralityGeneral (i : H ⟶ G) [Mono i.hom.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) : CommGroupScheme S :=
  (isCentral_of_artinian_baseChange_general i hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfArtinianCentralityGeneral_toGrp (i : H ⟶ G)
    [Mono i.hom.hom] [IsLocallyNoetherian (H.X ⊗ G.X).left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) :
    (commGroupSchemeOfArtinianCentralityGeneral i hc).toGrp = H := rfl

end Langlands.GroupScheme.ArtinianCentrality
