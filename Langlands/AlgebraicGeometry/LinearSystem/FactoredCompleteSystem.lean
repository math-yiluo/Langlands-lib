import Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem
import Langlands.AlgebraicGeometry.LinearSystem.LinearActionTwist
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.Modules.FlatSectionDescent

/-! # Section pullback for a factorization of a complete linear system -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Modules.DerivedSections

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem

local notation "Specᵣ " K:arg => Spec (CommRingCat.of K)

variable {K : Type u} [Field K] {X B : Over (Specᵣ K)} {N : LineBundle X.left}
  (C : CompleteGeneratingSystem X.hom N) (q : X ⟶ B) (g : B.left ⟶ ProjectiveSpace K C.n)
  (h : q.left ≫ g = C.map)

/-- The coordinate-preserving comparison of the twice-pulled-back twist with the line bundle
of a complete linear-system factorization. -/
def factoredTwistIso :
    (Scheme.Modules.pullback q.left).obj ((Scheme.Modules.pullback g).obj (twistOne K C.n)) ≅
      N.obj :=
  (Scheme.Modules.pullbackComp q.left g).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫
    linearSystemTwistIso X.hom (fun i ↦ C.basis i) C.generates

lemma factoredTwistIso_coordinate (i : Fin (C.n + 1)) :
    (C.factoredTwistIso q g h).hom.app ⊤
      (pullbackSection q.left ((Scheme.Modules.pullback g).obj (twistOne K C.n))
        (pullbackSection g (twistOne K C.n) (twistOneCoordinate K C.n i))) = C.basis i := by
  exact (pullbackComp_comparison_coordinate q.left g h (twistOne K C.n)
    (linearSystemTwistIso X.hom (fun i ↦ C.basis i) C.generates).hom _).trans
      (linearSystemTwistIso_coordinate X.hom (fun i ↦ C.basis i) C.generates i)

include h in
/-- If a complete linear-system map factors through `q`, then pulling back the sections of
its descended twist along `q` is surjective. -/
lemma surjective_pullback_of_factorization :
    Function.Surjective
      (relativeGlobalSectionsPullback q ((Scheme.Modules.pullback g).obj (twistOne K C.n))) := by
  let M := (Scheme.Modules.pullback g).obj (twistOne K C.n)
  let L := (relativeGlobalSectionsPullback q M).hom
  let E := ((relativeGlobalSections X.hom).mapIso (C.factoredTwistIso q g h)).toLinearEquiv
  have hs : Function.Surjective (E.toLinearMap.comp L) := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← C.basis.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    let s : (relativeGlobalSections B.hom).obj M :=
      pullbackSection g (twistOne K C.n) (twistOneCoordinate K C.n i)
    refine ⟨s, ?_⟩
    change E (relativeGlobalSectionsPullback q M s) = _
    rw [relativeGlobalSectionsPullback_apply]
    exact C.factoredTwistIso_coordinate q g h i
  change Function.Surjective L
  intro s
  obtain ⟨t, ht⟩ := hs (E s)
  exact ⟨t, E.injective ht⟩

/-- Along a flat surjective factorization map, pullback gives an equivalence between the
section spaces of the descended twist and its pullback. -/
def factoredSectionsEquiv [Flat q.left] [Surjective q.left] :
    (relativeGlobalSections B.hom).obj ((Scheme.Modules.pullback g).obj (twistOne K C.n)) ≃ₗ[K]
      (relativeGlobalSections X.hom).obj ((Scheme.Modules.pullback q.left).obj
        ((Scheme.Modules.pullback g).obj (twistOne K C.n))) :=
  LinearEquiv.ofBijective (relativeGlobalSectionsPullback q _).hom ⟨by
    intro s t hs
    apply Langlands.AlgebraicGeometry.Modules.pullbackSection_injective q.left _
    exact ((relativeGlobalSectionsPullback_apply q _ s).symm.trans hs).trans
      (relativeGlobalSectionsPullback_apply q _ t),
    C.surjective_pullback_of_factorization q g h⟩

end Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem
