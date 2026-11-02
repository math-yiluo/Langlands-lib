import Langlands.AlgebraicGeometry.LinearSystem.BundleComparison
import Langlands.AlgebraicGeometry.LinearSystem.CoordinateChange

/-! # Source equivariance of linear-system morphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {L : LineBundle X} {M : LineBundle Y} {n : ℕ}
  (s : Fin (n + 1) → GlobalSections L.obj)

/-- Pull back the ordered sections and transport them through a line-bundle
isomorphism on the source. -/
def transportedPullbackSections (f : Y ⟶ X)
    (b : ((LineBundle.pullback f).obj L).obj ≅ M.obj) :
    Fin (n + 1) → GlobalSections M.obj :=
  mapIsoSections b (fun i ↦ pullbackSection f L.obj (s i))

/-- Transported pullback sections generate at every source point. -/
lemma transportedPullbackSections_generate (f : Y ⟶ X)
    (b : ((LineBundle.pullback f).obj L).obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    ∀ y : Y, ∃ i, y ∈ nonvanishingLocus M.obj
      (transportedPullbackSections s f b i) :=
  mapIsoSections_generate b (pullbackSections_generate f hs)

/-- The actual morphism defined by transported pullback sections is the
original linear-system morphism precomposed with the source morphism. -/
lemma linearSystemMap_transportedPullback {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X)
    (b : ((LineBundle.pullback f).obj L).obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap (f ≫ p) (transportedPullbackSections_generate s f b hs) =
      f ≫ linearSystemMap p hs :=
  (linearSystemMap_mapIso (f ≫ p) b (pullbackSections_generate f hs)).trans
    (linearSystemMap_pullback p f hs)

/-- The same comparison holds over an arbitrary base scheme and after a
compatible change of base. -/
lemma relativeLinearSystemMap_transportedPullback {S S' : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S') (f : Y ⟶ X) (g : S' ⟶ S)
    (w : f ≫ p = q ≫ g)
    (b : ((LineBundle.pullback f).obj L).obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap q (transportedPullbackSections_generate s f b hs) ≫
        RelativeProjectiveSpace.map n g =
      f ≫ relativeLinearSystemMap p hs := by
  change relativeLinearSystemMap q
    (mapIsoSections_generate b (pullbackSections_generate f hs)) ≫ _ = _
  rw [relativeLinearSystemMap_mapIso]
  exact relativeLinearSystemMap_pullback p q f g w hs

/-- A source morphism preserving the base and carrying the pulled-back sections
to their linear coordinate change acts equivariantly on the actual projective
linear-system morphism. -/
lemma linearSystemMap_equivariant {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (f : X ⟶ X)
    (w : f ≫ p = p)
    (b : ((LineBundle.pullback f).obj L).obj ≅ L.obj)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hsections : transportedPullbackSections s f b =
      linearChangeSections p s e.toLinearMap)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    f ≫ linearSystemMap p hs = linearSystemMap p hs ≫ linearAction K n e := by
  have h : linearSystemMap p (linearChangeSections_generate p s e hs) =
      f ≫ linearSystemMap p hs := by
    simpa only [w, hsections] using linearSystemMap_transportedPullback s p f b hs
  exact h.symm.trans (linearSystemMap_linearChange p s e hs).symm

end Langlands.AlgebraicGeometry.LinearSystem
