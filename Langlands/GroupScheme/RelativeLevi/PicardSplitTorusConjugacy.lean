import Langlands.GroupScheme.GlobalSubgroupConjugacy
import Langlands.GroupScheme.Torus.LineBundlePicardCocycle
import Langlands.GroupScheme.AffineConjugatingCover
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.RelativeLevi.BorelTorusProjection
import Langlands.GroupScheme.RelativeLevi.SelfNormalizerProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Global conjugacy of split maximal tori in a common Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- Ambient fibrewise maximality restricts through a closed subgroup. -/
theorem IsFibrewiseMaximalTorus.of_comp
    {S : Scheme.{u}} {T : CommGroupScheme S} {B G : GroupScheme S}
    {t : T.toGrp ⟶ B} {i : B ⟶ G}
    (hi : IsClosedSubgroup i) (ht : IsFibrewiseMaximalTorus (t ≫ i)) :
    IsFibrewiseMaximalTorus t := by
  intro s
  have h := ht s
  rw [Functor.map_comp] at h
  exact IsMaximalTorus.of_comp (hi.baseChange (S.fromSpecResidueField s)) h

namespace splitTorus

variable {S : Scheme.{u}} [IsAffine S] {H : GroupScheme S}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  {I I' : Type u} [Finite I] [Finite I']
  (t : splitTorus S I ⟶ H) (t' : splitTorus S I' ⟶ H)
  (ht : IsClosedSubgroup t)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme S I) t)
  (ht' : IsClosedSubgroup t')
  (hmax' : IsFibrewiseMaximalTorus (T := commGroupScheme S I') t')
  (hself : (SubgroupFunctor.range t).normalizer = SubgroupFunctor.range t)
  (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))

include ht hmax ht' hmax' hself hPic in
/-- A self-normalizing split maximal torus is globally conjugate to every
split maximal torus of a smooth affine group over an affine Picard-trivial base. -/
theorem exists_conjugatingPoint_of_selfNormalizing :
    ∃ g : Over.mk (𝟙 S) ⟶ H.X,
      SubgroupFunctor.range (t ≫ (H.innerIso g).hom) = SubgroupFunctor.range t' := by
  let : Mono t.hom.hom := ht.mono_overHom
  let : Mono t'.hom.hom := ht'.mono_overHom
  obtain ⟨𝒰, hg⟩ := etaleLocalMaximalTorusConjugacy S H
    (commGroupScheme S I) (commGroupScheme S I') t t'
    (RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)) ht hmax
    (RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I')) ht' hmax'
  obtain ⟨U, hU, he, hs, g, hg⟩ :=
    AffineConjugatingCover.hasAffineEtaleConjugatingCover_of_range_cover t t' 𝒰 hg
  let : IsAffine U.left := hU
  let : Etale U.hom := he
  let : Surjective U.hom := hs
  let ξ := (Cocycle.coboundary g⁻¹).lift t (hg.coboundary_inv_lifts t t' hself)
  have hξ : ξ.IsTrivial := ξ.isTrivial_split_of_lineBundlesTrivial hPic
  exact ⟨SubgroupFunctor.globalConjugatingPoint t t' g hg hself hξ,
    SubgroupFunctor.globalConjugatingPoint_spec t t' g hg hself hξ⟩

end splitTorus

namespace RelativeLevi

variable {S : Scheme.{u}} [IsAffine S] {G B : GroupScheme S}
  (i : B ⟶ G) (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i)
  {I I' : Type u} [Finite I] [Finite I']
  (t : splitTorus S I ⟶ B) (t' : splitTorus S I' ⟶ B)
  (ht : IsClosedSubgroup (t ≫ i))
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) (t ≫ i))
  (ht' : IsClosedSubgroup (t' ≫ i))
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') (t' ≫ i))
  (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))

include hG hi ht hmax ht' hmax' hPic in
/-- Two supplied split ambient maximal tori in a common Borel are conjugate
by an actual section of that Borel over the affine base. -/
theorem exists_commonBorelSplitTorusConjugatingPoint :
    ∃ b : Over.mk (𝟙 S) ⟶ B.X,
      SubgroupFunctor.range (t ≫ (B.innerIso b).hom) = SubgroupFunctor.range t' := by
  let : Smooth B.X.hom := hi.1.smooth
  let : IsAffineHom B.X.hom := hi.1.isAffineHom
  have hiClosed := relativeParabolicClosed S G B i hG hi.1
  have hself : (SubgroupFunctor.range t).normalizer = SubgroupFunctor.range t :=
    relativeLeviSelfNormalizer S G B (splitTorus S I) i t hG hi.1
      (hi.isRelativeLeviSubgroup_of_maximalTorus hG
        (splitTorus.commGroupScheme S I) t
        (RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)) ht hmax)
  exact splitTorus.exists_conjugatingPoint_of_selfNormalizing t t'
    (IsClosedSubgroup.of_comp hiClosed ht) (hmax.of_comp hiClosed)
    (IsClosedSubgroup.of_comp hiClosed ht') (hmax'.of_comp hiClosed) hself hPic

/-- Choose a global conjugating section in the common Borel itself. -/
def commonBorelSplitTorusConjugatingPoint : Over.mk (𝟙 S) ⟶ B.X :=
  Classical.choose (exists_commonBorelSplitTorusConjugatingPoint
    i hG hi t t' ht hmax ht' hmax' hPic)

/-- The chosen section conjugates the complete represented torus ranges in B. -/
theorem commonBorelSplitTorusConjugatingPoint_spec :
    SubgroupFunctor.range (t ≫ (B.innerIso
      (commonBorelSplitTorusConjugatingPoint i hG hi t t' ht hmax ht' hmax' hPic)).hom) =
      SubgroupFunctor.range t' :=
  Classical.choose_spec (exists_commonBorelSplitTorusConjugatingPoint
    i hG hi t t' ht hmax ht' hmax' hPic)

end RelativeLevi

end Langlands.GroupScheme
