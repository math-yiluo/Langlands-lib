import Langlands.GroupScheme.GlobalSubgroupConjugacy
import Langlands.GroupScheme.Torus.LineBundlePicardCocycle
import Langlands.GroupScheme.WeilSolvableCocycle
import Langlands.GroupScheme.RelativeLevi.SplitBorelContainmentReduction

/-! # Global conjugacy from a split Borel vector-kernel presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

namespace Cocycle

variable {R : CommRingCat.{u}} {K H : GroupScheme (Spec R)}
  {I : Type u} [Finite I]
  (j : K ⟶ H) (q : H ⟶ splitTorus (Spec R) I) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  (σ : (splitTorus (Spec R) I).X ⟶ H.X)
  (hσ : σ ≫ q.hom.hom = 𝟙 _)
  [IsAffineHom K.X.hom] {n : ℕ} (hK : HasAffineVectorSeries n K)
  (hPic : ∀ L : LineBundle (Spec R), Nonempty (L ≅ LineBundle.trivial (Spec R)))
  {U : Over (Spec R)} [Flat U.hom] [Surjective U.hom]
  [LocallyOfFinitePresentation U.hom]

include hjq hσ hK hPic in
/-- A split torus quotient with a scheme section and a finite affine
vector-series kernel has trivial fppf cocycles under the actual Picard hypothesis. -/
theorem isTrivial_of_splitVectorExtension_lineBundlesTrivial
    (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_extension_section j q hjq σ hσ
    (fun ζ => ζ.isTrivial_fppf_of_hasAffineVectorSeries hK)
    ((ξ.map q).isTrivial_split_fppf_of_lineBundlesTrivial hPic)

end Cocycle

namespace RelativeLevi

variable {R : Type u} [CommRing R]
  {G B B' K : GroupScheme (Spec (CommRingCat.of R))}
  (i : B ⟶ G) (i' : B' ⟶ G) (hG : IsReductive G)
  (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
  {I : Type u} [Finite I]
  (j : K ⟶ B) (q : B ⟶ splitTorus (Spec (CommRingCat.of R)) I)
  [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  (σ : (splitTorus (Spec (CommRingCat.of R)) I).X ⟶ B.X)
  (hσ : σ ≫ q.hom.hom = 𝟙 _)
  [IsAffineHom K.X.hom] {n : ℕ} (hK : HasAffineVectorSeries n K)
  (hPic : ∀ L : LineBundle (Spec (CommRingCat.of R)),
    Nonempty (L ≅ LineBundle.trivial (Spec (CommRingCat.of R))))

include hG hi hi' hjq hσ hK hPic in
/-- Every relative Borel is conjugate over the original affine base to a
supplied Borel with a split torus quotient and a finite affine vector kernel. -/
theorem exists_globalSplitVectorBorelConjugatingPoint :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      SubgroupFunctor.range (i ≫ (G.innerIso g).hom) = SubgroupFunctor.range i' := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : Mono i'.hom.hom := hi'.isRelativeParabolicSubgroup.mono
  have hself : (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i :=
    relativeParabolicSelfNormalizer R G B i hG hi.isRelativeParabolicSubgroup.smooth
      (relativeParabolicClosed _ _ _ _ hG hi.isRelativeParabolicSubgroup)
      (fun k _ _ => hi.isRelativeParabolicSubgroup.isParabolicSubgroup_baseChange hG
        (Spec.algebraMap R k))
  obtain ⟨U, hU, he, hs, g, hg⟩ :=
    AffineConjugatingCover.hasAffineEtaleConjugatingCover_of_borels i i' hG hi hi'
  let : IsAffine U.left := hU
  let : Etale U.hom := he
  let : Surjective U.hom := hs
  let ξ := (Cocycle.coboundary g⁻¹).lift i (hg.coboundary_inv_lifts i i' hself)
  have hξ : ξ.IsTrivial :=
    ξ.isTrivial_of_splitVectorExtension_lineBundlesTrivial j q hjq σ hσ hK hPic
  refine ⟨SubgroupFunctor.globalConjugatingPoint i i' g hg hself hξ, ?_⟩
  exact SubgroupFunctor.globalConjugatingPoint_spec i i' g hg hself hξ

/-- Choose an actual global conjugator for the supplied split-vector Borel. -/
def globalSplitVectorBorelConjugatingPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X :=
  Classical.choose (exists_globalSplitVectorBorelConjugatingPoint
    i i' hG hi hi' j q hjq σ hσ hK hPic)

/-- The chosen point conjugates the full represented Borel subgroup functors. -/
theorem globalSplitVectorBorelConjugatingPoint_spec :
    SubgroupFunctor.range (i ≫ (G.innerIso
      (globalSplitVectorBorelConjugatingPoint i i' hG hi hi' j q hjq σ hσ hK hPic)).hom) =
      SubgroupFunctor.range i' :=
  Classical.choose_spec (exists_globalSplitVectorBorelConjugatingPoint
    i i' hG hi hi' j q hjq σ hσ hK hPic)

end RelativeLevi

end Langlands.GroupScheme
