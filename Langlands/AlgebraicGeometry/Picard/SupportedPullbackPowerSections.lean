import Langlands.AlgebraicGeometry.Modules.LineBundleSectionSupport
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionGeometry

/-! # Supported sections of actual pulled-back tensor powers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection

/-- Flatten a power of an upstairs tensor power and identify it with the actual
pullback of the corresponding downstairs tensor power. -/
def supportedPullbackTensorPowIso {X Y : Scheme.{u}} (q : Y ⟶ X)
    (L : LineBundle X) (n m : ℕ) :
    tensorPow (tensorPow ((Scheme.Modules.pullback q).obj L.obj) n) m ≅
      (Scheme.Modules.pullback q).obj (tensorPow L.obj (n * m)) :=
  tensorPowMulIso ((Scheme.Modules.pullback q).obj L.obj) n m ≪≫
    (actualPullbackTensorPowIso q L.obj (n * m)).symm

/-- If a positive-power upstairs section has empty generation open after a
quasi-compact pullback, a section of an actual pulled-back positive power has
the same generation open and vanishes after that pullback. -/
lemma exists_vanishing_pullback_powerSection {X Y T : Scheme.{u}}
    (q : Y ⟶ X) (i : T ⟶ Y) [CompactSpace T] (L : LineBundle X)
    {n : ℕ} (hn : 1 ≤ n) (s : ((LineBundle.pullback q).obj L).powSections n)
    (hs : i ⁻¹ᵁ ((LineBundle.pullback q).obj L).sectionOpen s = ⊥) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ t : GlobalSections ((Scheme.Modules.pullback q).obj (tensorPow L.obj r)),
        trivializationOpen ((Scheme.Modules.pullback q).obj (tensorPow L.obj r)) t =
            ((LineBundle.pullback q).obj L).sectionOpen s ∧
          pullbackSection i ((Scheme.Modules.pullback q).obj (tensorPow L.obj r)) t = 0 := by
  let M : LineBundle Y :=
    ⟨tensorPow ((Scheme.Modules.pullback q).obj L.obj) n,
      tensorPow_isLocallyFreeRankOne Y ((LineBundle.pullback q).obj L) n⟩
  obtain ⟨m, hm, hz⟩ := exists_pos_pullback_sectionPow_eq_zero i M s hs
  let e := supportedPullbackTensorPowIso q L n m
  refine ⟨n * m, by simpa using Nat.mul_le_mul hn hm,
    e.hom.app ⊤ (sectionPow M.obj s m), ?_, ?_⟩
  · exact (trivializationOpen_mapIso e _).trans
      (trivializationOpen_sectionPow M s (lt_of_lt_of_le Nat.zero_lt_one hm))
  · exact (pullbackSection_mapIso_eq_zero_iff i e _).mpr hz

/-- At a point above any chosen downstairs neighbourhood, an actual pulled-back
positive-power section generates and vanishes on the base change of the closed
complement. The complement after base change need not be reduced. -/
lemma exists_vanishing_upstairs_section (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X)
    (hL : ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ y : (pullback p b : Scheme.{u}), pullback.fst p b y = x ∧
      ∃ r : ℕ, 1 ≤ r ∧
        ∃ t : GlobalSections
          ((Scheme.Modules.pullback (pullback.fst p b)).obj (tensorPow L.obj r)),
          y ∈ trivializationOpen
              ((Scheme.Modules.pullback (pullback.fst p b)).obj (tensorPow L.obj r)) t ∧
            pullbackSection
              (pullback.snd (closedComplementι U) (pullback.fst p b))
              ((Scheme.Modules.pullback (pullback.fst p b)).obj (tensorPow L.obj r)) t = 0 := by
  let q := pullback.fst p b
  let i := closedComplementι U
  let i' := pullback.snd i q
  let : CompactSpace (pullback p b : Scheme.{u}) := hL.compactSpace
  let : CompactSpace (pullback i q : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace i'
  obtain ⟨y, hy, n, hn, s, hys, hsU⟩ :=
    exists_upstairs_section k K b X p L hL U x hx
  have hs : i' ⁻¹ᵁ ((LineBundle.pullback q).obj L).sectionOpen s = ⊥ := by
    apply bot_unique
    intro z hz
    have hzi : i (pullback.fst i q z) ∈ (U : Set X)ᶜ := by
      rw [← range_closedComplementι U]
      exact ⟨_, rfl⟩
    have hcomm : i (pullback.fst i q z) = q (i' z) := by
      exact congrArg (fun f => f z) (pullback.condition (f := i) (g := q))
    exact (hzi (hcomm ▸ hsU hz)).elim
  obtain ⟨r, hr, t, ht, hz⟩ :=
    exists_vanishing_pullback_powerSection q i' L hn s hs
  exact ⟨y, hy, r, hr, t, ht.symm ▸ hys, hz⟩

end Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection
