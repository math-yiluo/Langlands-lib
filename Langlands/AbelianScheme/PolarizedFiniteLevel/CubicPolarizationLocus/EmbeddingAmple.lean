import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry

/-! # Ampleness of the embedding bundle on the geometric fibres -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

open Picard Langlands.SchemeModule Langlands.Scheme.Modules

/-- Over an affine base the relative projective twist is ample. -/
lemma isAmple_twistOne (S : Scheme.{u}) [IsAffine S] (m : ℕ) : (twistOne S m).IsAmple := by
  refine ⟨QuasiCompact.compactSpace_of_compactSpace (toBase S m), fun x ↦ ?_⟩
  have hx : x ∈ (⨆ a, coordinateOpen S m a) := iSup_coordinateOpen S m ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let U : LineBundle (RelativeProjectiveSpace S m) := twistOne S m
  let s : U.powSections 1 := (tensorRightUnitor U.obj).inv.app ⊤ (twistOneCoordinate S m a)
  have hs : U.sectionOpen s = coordinateOpen S m a := by
    rw [← trivializationOpen_twistOneCoordinate S m a]
    exact trivializationOpen_mapIso (tensorRightUnitor U.obj).symm _
  exact ⟨1, le_rfl, s, hs ▸ ha, hs ▸ isAffineOpen_coordinateOpen S m a⟩

/-- The twist pulled back along a base-changed closed embedding into projective space is ample
    over every affine test scheme. -/
theorem isAmple_pullback_embedding {S T X : Scheme.{u}} [IsAffine T] (p : X ⟶ S)
    (m : ℕ) (i : X ⟶ RelativeProjectiveSpace S m) [IsClosedImmersion i]
    (hi : i ≫ toBase S m = p) (t : T ⟶ S) :
    ((LineBundle.pullback (pullback.fst p t ≫ i)).obj (twistOne S m)).IsAmple := by
  let a : pullback p t ⟶ pullback t (toBase S m) := pullback.lift
    (pullback.snd p t) (pullback.fst p t ≫ i) (by rw [Category.assoc, hi, pullback.condition])
  have hsnd : a ≫ pullback.snd t (toBase S m) = pullback.fst p t ≫ i := pullback.lift_snd _ _ _
  have ha : IsPullback (pullback.fst p t) a i (pullback.snd t (toBase S m)) := by
    have h : IsPullback (pullback.fst p t) (a ≫ pullback.fst t (toBase S m)) (i ≫ toBase S m) t := by
      rw [hi, show a ≫ pullback.fst t (toBase S m) = pullback.snd p t from pullback.lift_fst _ _ _]
      exact IsPullback.of_hasPullback p t
    exact h.of_bot hsnd.symm (IsPullback.of_hasPullback t (toBase S m)).flip
  have : IsClosedImmersion a := MorphismProperty.of_isPullback ha inferInstance
  let b := a ≫ (baseChangeIso m t).inv
  have : IsClosedImmersion b := by dsimp [b]; infer_instance
  have hb : b ≫ map m t = pullback.fst p t ≫ i := by
    change (a ≫ (baseChangeIso m t).inv) ≫ map m t = _
    rw [← baseChangeIso_hom_snd, Category.assoc, Iso.inv_hom_id_assoc, hsnd]
  have hamp := closedImmersionPullbackAmple _ _ b (twistOne T m) inferInstance (isAmple_twistOne T m)
  exact hamp.of_iso ((LineBundle.forget _).mapIso ((LineBundle.pullback b).mapIso
    (twistOnePullbackIso m t).symm ≪≫ LineBundle.pullbackCompEqIso b _ hb _))

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
