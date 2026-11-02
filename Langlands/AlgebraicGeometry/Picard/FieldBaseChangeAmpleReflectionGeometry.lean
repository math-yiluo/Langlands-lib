import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionSetup
import Langlands.AlgebraicGeometry.Modules.QCQSLineBundleSectionsBaseChange
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof

/-! # Actual sections and affine generation opens for field ampleness reflection -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection

/-- The square for an arbitrary morphism of field spectra, written using its actual
ring map. -/
lemma fieldProjection_isPullback (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) :
    IsPullback (pullback.fst p b) (pullback.snd p b) p
      (Spec.map (Spec.preimage b)) := by
  simpa only [Spec.map_preimage] using IsPullback.of_hasPullback p b

/-- If one specified line bundle becomes ample after field base change, then the
canonical scalar sections comparison is an isomorphism for every line bundle. -/
def sectionsIsoOfAmpleBaseChange (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (L : LineBundle X)
    (hL : ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple)
    (M : LineBundle X) :
    (ModuleCat.extendScalars (Spec.preimage b).hom).obj
        ((relativeGlobalSections p).obj M.obj) ≅
      (relativeGlobalSections (pullback.snd p b)).obj
        ((Scheme.Modules.pullback (pullback.fst p b)).obj M.obj) := by
  have htop := compactSpace_and_quasiSeparatedSpace k K b X p L hL
  let : CompactSpace X := htop.1
  let : QuasiSeparatedSpace X := htop.2
  let : IsAffineHom b := inferInstance
  let : IsAffineHom (pullback.fst p b) :=
    MorphismProperty.pullback_fst p b (inferInstance : IsAffineHom b)
  let h := fieldProjection_isPullback k K b X p
  exact Modules.CechResolution.scalarSectionsBaseChangeIso_lineBundle_qcqs
    (Spec.preimage b) p (pullback.snd p b) (pullback.fst p b) h.w M h
    (RingHom.Flat.of_isField (Field.toIsField k) (Spec.preimage b).hom)

/-- A whole generation open contained in an affine open is affine. -/
lemma isAffineOpen_trivializationOpen_of_le {X : Scheme.{u}} (M : LineBundle X)
    (s : GlobalSections M.obj) (U : X.Opens) (hU : IsAffineOpen U)
    (hs : trivializationOpen M.obj s ≤ U) :
    IsAffineOpen (trivializationOpen M.obj s) := by
  have h := affineGenerationLocusIntersection X M s U hU
  rwa [inf_eq_right.mpr hs] at h

/-- A supported section of a positive actual tensor power supplies exactly the
affine whole generation open required by the ampleness definition. -/
lemma isAffineOpen_sectionOpen_of_le {X : Scheme.{u}} (L : LineBundle X)
    {n : ℕ} (s : L.powSections n) (U : X.Opens) (hU : IsAffineOpen U)
    (hs : L.sectionOpen s ≤ U) : IsAffineOpen (L.sectionOpen s) :=
  isAffineOpen_trivializationOpen_of_le
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ s U hU hs

/-- Above every downstairs point and chosen neighbourhood, ampleness gives a
positive-power section supported in its preimage and generating at a point above it. -/
lemma exists_upstairs_section (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X)
    (hL : ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ y : (pullback p b : Scheme.{u}), pullback.fst p b y = x ∧
      ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : ((LineBundle.pullback (pullback.fst p b)).obj L).powSections n,
          y ∈ ((LineBundle.pullback (pullback.fst p b)).obj L).sectionOpen s ∧
            ((LineBundle.pullback (pullback.fst p b)).obj L).sectionOpen s ≤
              pullback.fst p b ⁻¹ᵁ U := by
  let q := pullback.fst p b
  let : Surjective q := surjective_projection k K b X p
  obtain ⟨y, hy⟩ := q.surjective x
  have hyU : y ∈ q ⁻¹ᵁ U := by
    change q y ∈ U
    rwa [hy]
  obtain ⟨n, hn, s, hys, hsU⟩ :=
    ampleSectionOpenBasis_apply (pullback p b)
      ((LineBundle.pullback q).obj L) hL (q ⁻¹ᵁ U) y hyU
  exact ⟨y, hy, n, hn, s, hys, hsU⟩

end Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection
