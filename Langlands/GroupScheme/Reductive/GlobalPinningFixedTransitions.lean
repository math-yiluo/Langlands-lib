import Langlands.GroupScheme.Reductive.GlobalPinningTransitions
import Langlands.GroupScheme.Reductive.AffinePinnedFixedCoherence

/-! # Fixed pinned chart transitions and canonical comparison naturality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CoordinateRootDatum

section OneGroup

variable {S : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]
    {G : GroupScheme S} [IsAffineHom G.X.hom]
    (t : splitTorus S I ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (b : P.Base)
    (R R' : Type u) [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)

local notation "M" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R a
local notation "N" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R' a'

/-- The actual original-group chart transition is a fixed comparison for
the identity full root datum and the identical simple-root labels. -/
def affineFrameFixedComparison {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Spec (CommRingCat.of R'))
    (k : T ⟶ S) (hf : f ≫ a = k) (hg : g ≫ a' = k) :
    @AffinePinnedModel.FixedComparison M N
      (RootPairing.Equiv.id P) (fun _ => Iff.rfl) T f g := by
  refine ⟨affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg, ?_, ?_⟩
  · change (M).inclusionOver f ≫ _ =
      (@AffinePinnedModel.fixedTorusIso M M
        (RootPairing.Equiv.id P) T).hom ≫ (N).inclusionOver g
    rw [AffinePinnedModel.fixedTorusIso_id, Category.id_comp]
    exact affineFrameComparison_torus t P hG ht hmax hP F b R R' a a' f g k hf hg
  · intro A _ _ _ x hx hx' s
    change (M).rootVectorPoint f A x hx s ≫ _ =
      (N).rootVectorPoint g A x hx' s
    exact affineFrameComparison_pinning t P hG ht hmax hP F b R R' a a' f g k hf hg
      hF A x hx hx' s

/-- Packaging the transition adds only its fixed properties. -/
@[simp] theorem affineFrameFixedComparison_val {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Spec (CommRingCat.of R'))
    (k : T ⟶ S) (hf : f ≫ a = k) (hg : g ≫ a' = k) :
    (affineFrameFixedComparison t P hG ht hmax hP F hF b R R' a a' f g k hf hg).val =
      affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg := rfl

end OneGroup

section TwoGroups

variable {S : Scheme.{u}} {I J I' J' : Type u}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (hH : IsReductive H) (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (hQ : IsGlobalCoordinateRootDatumOf I' H t' Q)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (F' : AffineRootFrames t' Q) (hF' : AffineRootFrames.IsCoherent t' Q F')
    (b : P.Base) (c : Q.Base)
    (θ : RootPairing.Equiv Q P)
    (hθ : ∀ s : J', s ∈ c.support ↔ θ.indexEquiv s ∈ b.support)
    (R R' : Type u) [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)

local notation "M₀" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R a
local notation "M₁" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R' a'
local notation "N₀" => pinnedAffineModelOfFrames t' Q hH ht' hmax' hQ F' c R a
local notation "N₁" => pinnedAffineModelOfFrames t' Q hH ht' hmax' hQ F' c R' a'

include hF hF' in
/-- On every common scheme, canonical fixed comparisons commute with the
actual chart transitions of both original groups. -/
theorem canonicalAffineFrameComparison_naturality
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Spec (CommRingCat.of R'))
    (k : T ⟶ S) (hf : f ≫ a = k) (hg : g ≫ a' = k) :
    affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg ≪≫
        (@AffinePinnedModel.fixedComparison M₁ N₁ θ hθ T hAffine g g).val =
      (@AffinePinnedModel.fixedComparison M₀ N₀ θ hθ T hAffine f f).val ≪≫
        affineFrameComparison t' Q hH ht' hmax' hQ F' c R R' a a' f g k hf hg := by
  let e := @AffinePinnedModel.fixedComparison M₀ N₀ θ hθ T hAffine f f
  let d := @AffinePinnedModel.fixedComparison M₁ N₁ θ hθ T hAffine g g
  let p := affineFrameFixedComparison t P hG ht hmax hP F hF b R R' a a' f g k hf hg
  let q := affineFrameFixedComparison t' Q hH ht' hmax' hQ F' hF' c R R' a a' f g k hf hg
  have hl :
      AffinePinnedModel.PreservesFixedTorus θ (p.val ≪≫ d.val) ∧
        AffinePinnedModel.PreservesFixedPinning θ hθ (p.val ≪≫ d.val) := by
    simpa only [AffinePinnedModel.FixedComparison.trans, RootPairing.Equiv.comp_id] using
      (AffinePinnedModel.FixedComparison.trans
        (M := M₀) (N := M₁) (K := N₁)
        (RootPairing.Equiv.id P) (fun _ => Iff.rfl) θ hθ p d).property
  have hr :
      AffinePinnedModel.PreservesFixedTorus θ (e.val ≪≫ q.val) ∧
        AffinePinnedModel.PreservesFixedPinning θ hθ (e.val ≪≫ q.val) := by
    simpa only [AffinePinnedModel.FixedComparison.trans, RootPairing.Equiv.id_comp] using
      (AffinePinnedModel.FixedComparison.trans
        (M := M₀) (N := N₀) (K := N₁)
        θ hθ (RootPairing.Equiv.id Q) (fun _ => Iff.rfl) e q).property
  exact AffinePinnedModel.FixedComparison.eq_of_affineTheorem_scheme
    (M := M₀) (N := N₁) θ hθ hAffine
    ⟨p.val ≪≫ d.val, hl⟩ ⟨e.val ≪≫ q.val, hr⟩

end TwoGroups

end Langlands.GroupScheme.CoordinateRootDatum
