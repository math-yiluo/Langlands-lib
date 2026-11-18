import Langlands.GroupScheme.LocalGroupIsoCoproductClassification
import Langlands.GroupScheme.RelativeUnipotent.FreeBundleMatrices
import Langlands.GroupScheme.RelativeUnipotent.SectionDescent

/-! # Actual module maps from natural linear free-section transformations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.SourceFreeSectionReconstruction

variable {S : Scheme.{u}}

/-- The actual map from a test to the identity test over its base. -/
def toIdentity (T : Over S) : T ⟶ Over.mk (𝟙 S) :=
  LocalGroupIso.terminalBasePoint T

/-- Identity pullback of a global section is the inverse canonical identity comparison. -/
lemma pullbackSection_identity (B : S.Modules) (s : GlobalSections B) :
    pullbackSection (𝟙 S) B s =
      ((Scheme.Modules.pullbackId S).inv.app B).app ⊤ s := by
  have H : ((Scheme.Modules.pullbackId S).hom.app B).app ⊤
      (pullbackSection (𝟙 S) B s) = s := by
    rw [pullbackSection_eq_sectionPullback]
    exact Langlands.Scheme.Modules.sectionPullback_id B ⊤ s
  have hi := congrArg (fun t => ((Scheme.Modules.pullbackId S).inv.app B).app ⊤ t) H
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using hi

/-- Canonical relative pullback of an identity-test section is ordinary
pullback of its actual global section on the base. -/
lemma sectionPullback_toIdentity (B : S.Modules) (T : Over S)
    (s : GlobalSections ((Scheme.Modules.pullback (𝟙 S)).obj B)) :
    sectionPullback B (toIdentity T) s =
      pullbackSection T.hom B (((Scheme.Modules.pullbackId S).hom.app B).app ⊤ s) := by
  let t := ((Scheme.Modules.pullbackId S).hom.app B).app ⊤ s
  have hs : pullbackSection (𝟙 S) B t = s := by
    rw [pullbackSection_identity]
    simp only [t, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
    rfl
  change sectionPullback B (toIdentity T) s = pullbackSection T.hom B t
  conv_lhs => rw [← hs]
  exact AffineSectionCoordinates.sectionPullback_pullbackSection B (toIdentity T) t

/-- A natural linear map from free coordinate sections to actual sections of
one fixed target sheaf, on every scheme test. -/
structure Transformation (n : ℕ) (B : S.Modules) where
  app : ∀ T : Over S,
    (Fin n → Γ(T.left, ⊤)) →ₗ[Γ(T.left, ⊤)]
      GlobalSections ((Scheme.Modules.pullback T.hom).obj B)
  natural : ∀ (T W : Over S) (b : W ⟶ T) (x : Fin n → Γ(T.left, ⊤)),
    app W (fun i => b.left.appTop (x i)) = sectionPullback B b (app T x)

namespace Transformation

variable {n : ℕ} {B : S.Modules} (C : Transformation n B)

/-- Original global section images, recovered from the actual identity-test map. -/
def images (i : Fin n) : GlobalSections B :=
  ((Scheme.Modules.pullbackId S).hom.app B).app ⊤
    (C.app (Over.mk (𝟙 S)) (Pi.single i 1))

/-- The natural transformation constructs an actual module-sheaf morphism. -/
def moduleHom : freeBundle S n ⟶ B :=
  FreeBundleMatrices.homOfSections n B C.images

/-- The derived original generator images pull back to the original test
transformation on each coordinate vector. -/
lemma images_pullback (T : Over S) (i : Fin n) :
    pullbackSection T.hom B (C.images i) = C.app T (Pi.single i 1) := by
  classical
  have H := C.natural (Over.mk (𝟙 S)) T (toIdentity T) (Pi.single i 1)
  have hb : (fun j => (toIdentity T).left.appTop ((Pi.single i 1 : Fin n → Γ(S, ⊤)) j)) =
      (Pi.single i 1 : Fin n → Γ(T.left, ⊤)) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [hb, sectionPullback_toIdentity] at H
  exact H.symm

/-- The actual module map recovers the prescribed natural linear
transformation on every test, in the canonical free section coordinates. -/
lemma moduleHom_coordinates (T : Over S) (x : Fin n → Γ(T.left, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map C.moduleHom).app ⊤
        (freeBundleSectionEquiv n T x) = C.app T x := by
  classical
  rw [moduleHom, FreeBundleMatrices.homOfSections_coordinates]
  simp_rw [C.images_pullback]
  have hx : (∑ i, x i • (Pi.single i 1 : Fin n → Γ(T.left, ⊤))) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = C.app T (∑ i, x i • (Pi.single i 1 : Fin n → Γ(T.left, ⊤))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    _ = C.app T x := congrArg (C.app T) hx

end Transformation
end Langlands.GroupScheme.RelativeUnipotent.SourceFreeSectionReconstruction
