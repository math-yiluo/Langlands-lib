import Langlands.AlgebraicGeometry.Deformation.ArtinianSchemeDetection
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry

/-! # Detecting subgroup centrality on local Artinian base changes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ArtinianCentrality

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Commutation of the universal pair detects all-test-scheme centrality. -/
theorem isCentral_of_universal_commute (i : H ⟶ G)
    (hc : Commute (fst H.X G.X ≫ i.hom.hom) (snd H.X G.X)) : IsCentral i := by
  intro T x
  apply mem_center.mpr
  intro T' a y
  change (a ≫ x ≫ i.hom.hom) * y = y * (a ≫ x ≫ i.hom.hom)
  have ht := congrArg (fun z => lift (a ≫ x) y ≫ z) hc.eq
  simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc] using ht

/-- Local Artinian base changes detect centrality if the universal product is
locally noetherian and the ambient scheme is affine. -/
theorem isCentral_of_artinian_baseChange (i : H ⟶ G)
    [IsLocallyNoetherian (H.X ⊗ G.X).left] [IsAffine G.X.left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) : IsCentral i := by
  apply isCentral_of_universal_commute i
  apply Over.OverMorphism.ext
  apply Langlands.AlgebraicGeometry.Deformation.ArtinianDetection.hom_ext
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

/-- The unchanged monomorphic subgroup, bundled as commutative using its
centrality on every local Artinian base change. -/
def commGroupSchemeOfArtinianCentrality (i : H ⟶ G) [Mono i.hom.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left] [IsAffine G.X.left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) : CommGroupScheme S :=
  (isCentral_of_artinian_baseChange i hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfArtinianCentrality_toGrp (i : H ⟶ G) [Mono i.hom.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left] [IsAffine G.X.left]
    (hc : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
        IsCentral ((GroupScheme.baseChange b).map i)) :
    (commGroupSchemeOfArtinianCentrality i hc).toGrp = H := rfl

end Langlands.GroupScheme.ArtinianCentrality
