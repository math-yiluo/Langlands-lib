import Langlands.GroupScheme.Reductive.AffineSplitConjugacyTransport
import Langlands.GroupScheme.Reductive.PicardTrivialSplitCoordinates

/-! # The affine split torus and Borel conjugacy clause -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open SubgroupFunctor Langlands.AlgebraicGeometry.Picard

/-- The full affine conjugacy conclusion under exactly connectedness and
triviality of every actual line bundle, with no structural hypotheses retained. -/
theorem connectedPicardAffineSplitTorusBorelConjugacy
    (S : Scheme.{u}) [IsAffine S] [ConnectedSpace S]
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (G : GroupScheme S) (hG : IsReductive G)
    (I I' : Type u) [Finite I] [Finite I']
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t') :
    (∃ g : Over.mk (𝟙 S) ⟶ G.X,
      range (t ≫ (G.innerIso g).hom) = range t') ∧
    ∀ (B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G),
      IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup i' →
      range t ≤ range i → range t' ≤ range i' →
      ∃ g : Over.mk (𝟙 S) ⟶ G.X,
        range (t ≫ (G.innerIso g).hom) = range t' ∧
        range (i ≫ (G.innerIso g).hom) = range i' := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype I' := Fintype.ofFinite I'
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace (Spec Γ(S, ⊤)) :=
    (Scheme.homeoOfIso S.isoSpec).connectedSpace_iff.mp inferInstance
  let b := S.isoSpec.inv
  let F := GroupScheme.baseChange b
  let q := AffineSplitConjugacy.modelTorus t
  let q' := AffineSplitConjugacy.modelTorus t'
  have hPic' := lineBundlesTrivial_of_retract b S.isoSpec.hom S.isoSpec.inv_hom_id hPic
  have hq : IsClosedSubgroup q :=
    (ht.baseChange b).iso_comp (splitTorus.baseChangeIso b I).symm
  have hqm : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) q :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom I G t hmax b
  have hq' : IsClosedSubgroup q' :=
    (ht'.baseChange b).iso_comp (splitTorus.baseChangeIso b I').symm
  have hqm' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') q' :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom I' G t' hmax' b
  have hseries : HasSplitBorelVectorSeries q :=
    hasSplitBorelVectorSeries_of_connected_of_lineBundlesTrivial
      hPic' I (F.obj G) (hG.baseChange b) q hq hqm
  have hseries' : HasSplitBorelVectorSeries q' :=
    hasSplitBorelVectorSeries_of_connected_of_lineBundlesTrivial
      hPic' I' (F.obj G) (hG.baseChange b) q' hq' hqm'
  constructor
  · obtain ⟨g, hg⟩ := hseries.exists_torusConjugatingPoint
      hseries' (hG.baseChange b) hPic' hq hqm hq' hqm'
    have hr : range (q ≫ ((F.obj G).innerIso g).hom) =
        range (F.map t ≫ ((F.obj G).innerIso g).hom) := by
      exact (congrArg range (Category.assoc _ _ _)).trans
        (range_iso_comp (splitTorus.baseChangeIso b I).symm
          (F.map t ≫ ((F.obj G).innerIso g).hom))
    have hg' : range (F.map t ≫ ((F.obj G).innerIso g).hom) = range (F.map t') :=
      hr.symm.trans (hg.trans
        (range_iso_comp (splitTorus.baseChangeIso b I').symm (F.map t')))
    exact ⟨retractBaseChangePoint b S.isoSpec.hom S.isoSpec.hom_inv_id G g,
      retractBaseChangePoint_spec b S.isoSpec.hom S.isoSpec.hom_inv_id t t' g hg'⟩
  · intro B B' i i' hi hi' hti hti'
    exact AffineSplitConjugacy.exists_simultaneousConjugatingPoint
      hG hPic t t' hseries ht hmax ht' hmax' B B' i i' hi hi' hti hti'

/-- A chosen actual affine split maximal torus conjugator under the original
connected scheme and line-bundle Picard hypotheses. -/
def picardAffineSplitTorusConjugatingPoint
    (S : Scheme.{u}) [IsAffine S] [ConnectedSpace S]
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (G : GroupScheme S) (hG : IsReductive G)
    (I I' : Type u) [Finite I] [Finite I']
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t') :
    Over.mk (𝟙 S) ⟶ G.X :=
  Classical.choose (connectedPicardAffineSplitTorusBorelConjugacy
    S hPic G hG I I' t t' ht hmax ht' hmax').1

/-- The chosen point carries the full represented first torus onto the second. -/
theorem picardAffineSplitTorusConjugatingPoint_spec
    (S : Scheme.{u}) [IsAffine S] [ConnectedSpace S]
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (G : GroupScheme S) (hG : IsReductive G)
    (I I' : Type u) [Finite I] [Finite I']
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t') :
    range (t ≫ (G.innerIso
      (picardAffineSplitTorusConjugatingPoint S hPic G hG I I' t t' ht hmax ht' hmax')).hom) =
      range t' :=
  Classical.choose_spec (connectedPicardAffineSplitTorusBorelConjugacy
    S hPic G hG I I' t t' ht hmax ht' hmax').1

end Langlands.GroupScheme
