import Langlands.GroupScheme.Reductive.AffineSplitTorusBorelConjugacy
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.GroupScheme.RelativeLevi.BorelTransport

/-! # Transport of affine split conjugacy from the ring model -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.Picard

/-- Triviality of all actual line bundles passes to a retract of the base. -/
theorem lineBundlesTrivial_of_retract {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (hba : b ≫ a = 𝟙 S')
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S)) :
    ∀ L : LineBundle S', Nonempty (L ≅ LineBundle.trivial S') := by
  intro L
  let M := (LineBundle.pullback a).obj L
  obtain ⟨e⟩ := hPic M
  let d : (LineBundle.pullback b).obj M ≅ L :=
    ObjectProperty.isoMk _
      ((Scheme.Modules.pullbackComp b a).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr hba).app L.obj ≪≫
          (Scheme.Modules.pullbackId S').app L.obj)
  exact ⟨d.symm ≪≫ (LineBundle.pullback b).mapIso e ≪≫ LineBundle.pullbackTrivialIso b⟩

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.GroupScheme

open SubgroupFunctor Langlands.AlgebraicGeometry.Picard

/-- Evaluate a pulled-back base section along a section of the base map. -/
def retractBaseChangePoint {S S' : Scheme.{u}} (b : S' ⟶ S) (a : S ⟶ S')
    (hab : a ≫ b = 𝟙 S) (G : GroupScheme S)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    Over.mk (𝟙 S) ⟶ G.X :=
  (show Over.mk (𝟙 S) ⟶ Over.mk b from Over.homMk a hab) ≫
    baseChangeBasePointsEquiv b G g

/-- Actual conjugacy ranges pull back along a section of the base map. -/
theorem retractBaseChangePoint_spec {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (hab : a ≫ b = 𝟙 S)
    {G H H' : GroupScheme S} (i : H ⟶ G) (i' : H' ⟶ G)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg : range ((GroupScheme.baseChange b).map i ≫
      (((GroupScheme.baseChange b).obj G).innerIso g).hom) =
        range ((GroupScheme.baseChange b).map i')) :
    range (i ≫ (G.innerIso (retractBaseChangePoint b a hab G g)).hom) = range i' := by
  have h := (isConjugatingPoint_iff_range_innerIso _ _ g).mpr hg
  rw [range_baseChangeHom, range_baseChangeHom] at h
  have hbase := (isConjugatingPoint_baseChangeBasePointsEquiv_iff b g).mp h
  exact (isConjugatingPoint_iff_range_innerIso i i' _).mp
    (hbase.restrict (show Over.mk (𝟙 S) ⟶ Over.mk b from Over.homMk a hab))

namespace HasSplitBorelVectorSeries

/-- Supplied split Borel series for both tori supply containing Borels for
the pair-only global conjugacy conclusion over a ring spectrum. -/
theorem exists_torusConjugatingPoint
    {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
    {I I' : Type u} [Fintype I] [Fintype I']
    {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {t' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G}
    (h : HasSplitBorelVectorSeries t) (h' : HasSplitBorelVectorSeries t')
    (hG : IsReductive G)
    (hPic : ∀ L : LineBundle (Spec (CommRingCat.of R)),
      Nonempty (L ≅ LineBundle.trivial (Spec (CommRingCat.of R))))
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t') :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      range (t ≫ (G.innerIso g).hom) = range t' := by
  have hseries := h
  obtain ⟨B, _, i, _, _, t₀, hi, _, _, hti, _⟩ := h
  obtain ⟨B', _, i', _, _, t₀', hi', _, _, hti', _⟩ := h'
  obtain ⟨g, hg, _⟩ := hseries.exists_simultaneousConjugatingPoint
    hG hPic t' ht hmax ht' hmax' B B' i i' hi hi'
    (range_le_of_factor t₀ hti) (range_le_of_factor t₀' hti')
  exact ⟨g, hg⟩

end HasSplitBorelVectorSeries

namespace AffineSplitConjugacy

variable {S : Scheme.{u}} [IsAffine S] {G : GroupScheme S}
    {I I' : Type u} [Fintype I] [Fintype I']

/-- The original coordinate torus map on the canonical ring model of an
affine base, using the specified split-torus base-change isomorphism. -/
abbrev modelTorus (t : splitTorus S I ⟶ G) :
    splitTorus (Spec Γ(S, ⊤)) I ⟶ (GroupScheme.baseChange S.isoSpec.inv).obj G :=
  (splitTorus.baseChangeIso S.isoSpec.inv I).inv ≫
    (GroupScheme.baseChange S.isoSpec.inv).map t

/-- Simultaneous conjugacy on the canonical ring model transports to an
actual section over the original affine scheme. -/
theorem exists_simultaneousConjugatingPoint
    (hG : IsReductive G)
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (h : HasSplitBorelVectorSeries (modelTorus t))
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t')
    (B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i') :
    ∃ g : Over.mk (𝟙 S) ⟶ G.X,
      range (t ≫ (G.innerIso g).hom) = range t' ∧
      range (i ≫ (G.innerIso g).hom) = range i' := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let b := S.isoSpec.inv
  let F := GroupScheme.baseChange b
  have hPic' := lineBundlesTrivial_of_retract b S.isoSpec.hom S.isoSpec.inv_hom_id hPic
  have htc : IsClosedSubgroup (modelTorus t) :=
    (ht.baseChange b).iso_comp (splitTorus.baseChangeIso b I).symm
  have htm : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme _ I) (modelTorus t) :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom I G t hmax b
  have htc' : IsClosedSubgroup (modelTorus t') :=
    (ht'.baseChange b).iso_comp (splitTorus.baseChangeIso b I').symm
  have htm' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme _ I') (modelTorus t') :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom I' G t' hmax' b
  have hti₀ : range (modelTorus t) ≤ range (F.map i) := by
    calc
      range (modelTorus t) = range (F.map t) :=
        range_iso_comp (splitTorus.baseChangeIso b I).symm (F.map t)
      _ ≤ range (F.map i) := by
        change range ((GroupScheme.baseChange b).map t) ≤ range ((GroupScheme.baseChange b).map i)
        rw [range_baseChangeHom, range_baseChangeHom]
        exact baseChange_mono b hti
  have hti₀' : range (modelTorus t') ≤ range (F.map i') := by
    calc
      range (modelTorus t') = range (F.map t') :=
        range_iso_comp (splitTorus.baseChangeIso b I').symm (F.map t')
      _ ≤ range (F.map i') := by
        change range ((GroupScheme.baseChange b).map t') ≤ range ((GroupScheme.baseChange b).map i')
        rw [range_baseChangeHom, range_baseChangeHom]
        exact baseChange_mono b hti'
  obtain ⟨g, htg, hig⟩ := h.exists_simultaneousConjugatingPoint
    (hG.baseChange b) hPic' (modelTorus t') htc htm htc' htm'
    (F.obj B) (F.obj B') (F.map i) (F.map i')
    (hi.baseChange hG b) (hi'.baseChange hG b) hti₀ hti₀'
  have htg' : range (F.map t ≫ ((F.obj G).innerIso g).hom) = range (F.map t') := by
    change range (((splitTorus.baseChangeIso b I).inv ≫ F.map t) ≫
      ((F.obj G).innerIso g).hom) = range ((splitTorus.baseChangeIso b I').inv ≫ F.map t') at htg
    have hr : range (((splitTorus.baseChangeIso b I).inv ≫ F.map t) ≫
        ((F.obj G).innerIso g).hom) = range (F.map t ≫ ((F.obj G).innerIso g).hom) := by
      simpa only [Category.assoc, Iso.symm_hom] using
        range_iso_comp (splitTorus.baseChangeIso b I).symm
          (F.map t ≫ ((F.obj G).innerIso g).hom)
    exact hr.symm.trans (htg.trans
      (range_iso_comp (splitTorus.baseChangeIso b I').symm (F.map t')))
  exact ⟨retractBaseChangePoint b S.isoSpec.hom S.isoSpec.hom_inv_id G g,
    retractBaseChangePoint_spec b S.isoSpec.hom S.isoSpec.hom_inv_id t t' g htg',
    retractBaseChangePoint_spec b S.isoSpec.hom S.isoSpec.hom_inv_id i i' g hig⟩

/-- A chosen simultaneous conjugator on the original affine scheme. -/
def simultaneousConjugatingPoint
    (hG : IsReductive G)
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G)
    (h : HasSplitBorelVectorSeries (modelTorus t))
    (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t)
    (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t')
    (B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hti : range t ≤ range i) (hti' : range t' ≤ range i') :
    Over.mk (𝟙 S) ⟶ G.X :=
  Classical.choose (exists_simultaneousConjugatingPoint
    hG hPic t t' h ht hmax ht' hmax' B B' i i' hi hi' hti hti')

end AffineSplitConjugacy

end Langlands.GroupScheme
