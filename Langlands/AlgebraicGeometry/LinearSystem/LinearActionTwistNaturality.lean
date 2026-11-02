import Langlands.AlgebraicGeometry.LinearSystem.RelativeLinearActionTwist
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison

/-! # Base change of the relative projective linear-action twist comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The inverse composition comparison carries a composite section to its iterated pullback. -/
lemma pullbackComp_inv_coordinate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤
        (pullbackSection (f ≫ g) M s) =
      pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s) := by
  rw [← pullbackSection_comp M g f s]
  change ((Scheme.Modules.pullbackComp f g).hom.app M ≫
    (Scheme.Modules.pullbackComp f g).inv.app M).app ⊤ _ = _
  rw [Iso.hom_inv_id_app]
  rfl

/-- The canonical square comparison preserves the twice pulled-back original section. -/
lemma squarePullbackIso_coordinate {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : p' ≫ b = a ≫ p) (M : Y.Modules) (s : GlobalSections M) :
    (Langlands.Scheme.Modules.squarePullbackIso p p' a b w M).hom.app ⊤
        (pullbackSection p' ((Scheme.Modules.pullback b).obj M) (pullbackSection b M s)) =
      pullbackSection a ((Scheme.Modules.pullback p).obj M) (pullbackSection p M s) := by
  change ((Scheme.Modules.pullbackComp p' b).hom.app M ≫
    (Scheme.Modules.pullbackCongr w).hom.app M ≫
    (Scheme.Modules.pullbackComp a p).inv.app M).app ⊤ _ = _
  rw [pullbackComp_comparison_coordinate, pullbackComp_inv_coordinate]

/-- On a covering family of frames, a square comparison is determined by its section formula. -/
lemma pullback_comparison_square {X Y : Scheme.{u}} {M : X.Modules} {N : Y.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (g : Y ⟶ X) (a : Y ⟶ Y) (b : X ⟶ X) (w : g ≫ b = a ≫ g)
    (δ : (Scheme.Modules.pullback g).obj M ⟶ N)
    (α : (Scheme.Modules.pullback a).obj N ⟶ N)
    (β : (Scheme.Modules.pullback b).obj M ⟶ M)
    (h : ∀ i,
      δ.app ⊤ (pullbackSection g M (β.app ⊤ (pullbackSection b M (s i)))) =
        α.app ⊤ (pullbackSection a N (δ.app ⊤ (pullbackSection g M (s i))))) :
    (Scheme.Modules.pullback g).map β ≫ δ =
      (Langlands.Scheme.Modules.squarePullbackIso g g a b w M).hom ≫
        (Scheme.Modules.pullback a).map δ ≫ α := by
  have hs' := frameCover_pullback hM s hs b
  have hs'' := frameCover_pullback (hM.pullback b)
    (fun i ↦ pullbackSection b M (s i)) hs' g
  apply hom_ext_of_generating_sections
    (fun i ↦ pullbackSection g ((Scheme.Modules.pullback b).obj M)
      (pullbackSection b M (s i))) hs''
  intro i
  rw [pullbackMap_comp_coordinate]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    squarePullbackIso_coordinate, pullbackMap_comp_coordinate]
  exact h i

/-- Pulling a scalar from the coefficient base commutes with simultaneous base and ring change. -/
lemma scalarsFromBase_baseChange {K R : Type u} [CommRing K] [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    (q : Y ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X) (φ : K →+* R)
    (w : q ≫ Spec.map (CommRingCat.ofHom φ) = g ≫ p) (r : K) :
    g.appTop (Scheme.Modules.scalarsFromBase p r) =
      Scheme.Modules.scalarsFromBase q (φ r) := by
  have hc : g.appTop (Scheme.Modules.scalarsFromBase p r) =
      Scheme.Modules.scalarsFromBase (g ≫ p) r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫ g.appTop) r = _
    rw [← Scheme.Hom.comp_appTop]
    rfl
  rw [hc, ← w, scalarsFromBase_specMap]
  rfl

/-- A coordinate-preserving pullback comparison preserves linear combinations after mapping coefficients. -/
lemma pullback_comparison_linearChange_baseChange
    {K R : Type u} [CommRing K] [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of R))
    {L : LineBundle X} {M : LineBundle Y} {n : ℕ}
    (s : Fin (n + 1) → GlobalSections L.obj)
    (t : Fin (n + 1) → GlobalSections M.obj) (g : Y ⟶ X) (φ : K →+* R)
    (w : q ≫ Spec.map (CommRingCat.ofHom φ) = g ≫ p)
    (δ : (Scheme.Modules.pullback g).obj L.obj ⟶ M.obj)
    (hδ : ∀ i, δ.app ⊤ (pullbackSection g L.obj (s i)) = t i)
    (e : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K))
    (e' : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R))
    (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i)
    (i : Fin (n + 1)) :
    δ.app ⊤ (pullbackSection g L.obj (linearChangeSections p s e i)) =
      linearChangeSections q t e' i := by
  simp only [linearChangeSections, linComb, pullbackSection_sum, pullbackSection_smul,
    map_sum, Scheme.Modules.Hom.app_smul, scalarsFromBase_baseChange p q g φ w,
    hcoeff, hδ]

/-- Linear coordinate laws and compatible coefficients imply the full square law. -/
lemma linearChange_pullback_comparison_square
    {K R : Type u} [CommRing K] [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of R))
    {L : LineBundle X} {M : LineBundle Y} {n : ℕ}
    (s : Fin (n + 1) → GlobalSections L.obj)
    (t : Fin (n + 1) → GlobalSections M.obj)
    (hs : (⨆ i, trivializationOpen L.obj (s i)) = ⊤)
    (g : Y ⟶ X) (φ : K →+* R)
    (wc : q ≫ Spec.map (CommRingCat.ofHom φ) = g ≫ p)
    (a : Y ⟶ Y) (b : X ⟶ X) (w : g ≫ b = a ≫ g)
    (δ : (Scheme.Modules.pullback g).obj L.obj ⟶ M.obj)
    (α : (Scheme.Modules.pullback a).obj M.obj ⟶ M.obj)
    (β : (Scheme.Modules.pullback b).obj L.obj ⟶ L.obj)
    (e : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K))
    (e' : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R))
    (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i)
    (hδ : ∀ i, δ.app ⊤ (pullbackSection g L.obj (s i)) = t i)
    (hα : ∀ i, α.app ⊤ (pullbackSection a M.obj (t i)) =
      linearChangeSections q t e' i)
    (hβ : ∀ i, β.app ⊤ (pullbackSection b L.obj (s i)) =
      linearChangeSections p s e i) :
    (Scheme.Modules.pullback g).map β ≫ δ =
      (Langlands.Scheme.Modules.squarePullbackIso g g a b w L.obj).hom ≫
        (Scheme.Modules.pullback a).map δ ≫ α := by
  apply pullback_comparison_square L.property s hs g a b w δ α β
  intro i
  rw [hβ, hδ, hα]
  exact pullback_comparison_linearChange_baseChange (L := L) (M := M)
    p q s t g φ wc δ hδ e e' hcoeff i

section Relative

variable {K R : Type u} [CommRing K] [CommRing R] {S T : Scheme.{u}} {n : ℕ}
  (a : S ⟶ Spec (CommRingCat.of K)) (b : T ⟶ Spec (CommRingCat.of R))
  (f : T ⟶ S) (φ : K →+* R)
  (w : b ≫ Spec.map (CommRingCat.ofHom φ) = f ≫ a)
  (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
  (e' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
  (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i)

/-- Base change of the actual relative twist comparison followed by the canonical twist identification. -/
def relativeLinearActionTwistBaseChangeIso :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.map n f)).obj
        ((Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction a e)).obj
          (RelativeProjectiveSpace.twistOne S n).obj) ≅
      (RelativeProjectiveSpace.twistOne T n).obj :=
  (Scheme.Modules.pullback (RelativeProjectiveSpace.map n f)).mapIso
      (relativeLinearActionTwistIso a e) ≪≫
    (LineBundle.forget _).mapIso (RelativeProjectiveSpace.twistOnePullbackIso n f)

include w hcoeff in
/-- The base twist comparison transports all transformed coordinates with their mapped coefficients. -/
lemma twistOnePullbackIso_changed_coordinate (i : Fin (n + 1)) :
    (RelativeProjectiveSpace.twistOnePullbackIso n f).hom.hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.map n f)
          (RelativeProjectiveSpace.twistOne S n).obj
          (changedRelativeProjectiveCoordinates a e i)) =
      changedRelativeProjectiveCoordinates b e' i := by
  apply pullback_comparison_linearChange_baseChange
    (L := RelativeProjectiveSpace.twistOne S n) (M := RelativeProjectiveSpace.twistOne T n)
    (RelativeProjectiveSpace.toBase S n ≫ a) (RelativeProjectiveSpace.toBase T n ≫ b)
    (RelativeProjectiveSpace.twistOneCoordinate S n) (RelativeProjectiveSpace.twistOneCoordinate T n)
    (RelativeProjectiveSpace.map n f) φ _
    (RelativeProjectiveSpace.twistOnePullbackIso n f).hom.hom
    (RelativeProjectiveSpace.twistOnePullbackIso_coordinate n f) e.toLinearMap e'.toLinearMap hcoeff i
  simp only [Category.assoc, w, RelativeProjectiveSpace.map_toBase_assoc]

include w hcoeff in
/-- The base-changed action comparison sends every twice pulled-back coordinate to its changed coordinate. -/
lemma relativeLinearActionTwistBaseChangeIso_coordinate (i : Fin (n + 1)) :
    (relativeLinearActionTwistBaseChangeIso a f e).hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.map n f)
          ((Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction a e)).obj
            (RelativeProjectiveSpace.twistOne S n).obj)
          (pullbackSection (RelativeProjectiveSpace.linearAction a e)
            (RelativeProjectiveSpace.twistOne S n).obj
            (RelativeProjectiveSpace.twistOneCoordinate S n i))) =
      changedRelativeProjectiveCoordinates b e' i := by
  change ((Scheme.Modules.pullback (RelativeProjectiveSpace.map n f)).map
    (relativeLinearActionTwistIso a e).hom ≫
    (RelativeProjectiveSpace.twistOnePullbackIso n f).hom.hom).app ⊤ _ = _
  rw [pullbackMap_comp_coordinate, relativeLinearActionTwistIso_coordinate]
  exact twistOnePullbackIso_changed_coordinate a b f φ w e e' hcoeff i

/-- The actual relative linear-action twist comparison is natural for simultaneous base and coefficient change. -/
lemma relativeLinearActionTwistBaseChangeIso_naturality :
    relativeLinearActionTwistBaseChangeIso a f e =
      Langlands.Scheme.Modules.squarePullbackIso
          (RelativeProjectiveSpace.map n f) (RelativeProjectiveSpace.map n f)
          (RelativeProjectiveSpace.linearAction b e') (RelativeProjectiveSpace.linearAction a e)
          (RelativeProjectiveSpace.map_linearAction_coefficientMap a b f φ w e e' hcoeff)
          (RelativeProjectiveSpace.twistOne S n).obj ≪≫
        (Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction b e')).mapIso
          ((LineBundle.forget _).mapIso (RelativeProjectiveSpace.twistOnePullbackIso n f)) ≪≫
        relativeLinearActionTwistIso b e' := by
  apply Iso.ext
  apply linearChange_pullback_comparison_square
    (L := RelativeProjectiveSpace.twistOne S n) (M := RelativeProjectiveSpace.twistOne T n)
    (RelativeProjectiveSpace.toBase S n ≫ a) (RelativeProjectiveSpace.toBase T n ≫ b)
    (RelativeProjectiveSpace.twistOneCoordinate S n) (RelativeProjectiveSpace.twistOneCoordinate T n)
    (isOpenCover_trivializationOpen (L := RelativeProjectiveSpace.twistOne S n)
      (relativeProjectiveCoordinates_generate S n))
    (RelativeProjectiveSpace.map n f) φ _
    (RelativeProjectiveSpace.linearAction b e') (RelativeProjectiveSpace.linearAction a e)
    (RelativeProjectiveSpace.map_linearAction_coefficientMap a b f φ w e e' hcoeff)
    (RelativeProjectiveSpace.twistOnePullbackIso n f).hom.hom
    (relativeLinearActionTwistIso b e').hom (relativeLinearActionTwistIso a e).hom
    e.toLinearMap e'.toLinearMap hcoeff
    (RelativeProjectiveSpace.twistOnePullbackIso_coordinate n f)
    (relativeLinearActionTwistIso_coordinate b e') (relativeLinearActionTwistIso_coordinate a e)
  simp only [Category.assoc, w, RelativeProjectiveSpace.map_toBase_assoc]

end Relative

/-- Base change of the action comparison for a matrix of global functions. -/
abbrev globalLinearActionTwistBaseChangeIso {S T : Scheme.{u}} (n : ℕ) (f : T ⟶ S)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.map n f)).obj
        ((Scheme.Modules.pullback (RelativeProjectiveSpace.globalLinearAction n e)).obj
          (RelativeProjectiveSpace.twistOne S n).obj) ≅
      (RelativeProjectiveSpace.twistOne T n).obj :=
  relativeLinearActionTwistBaseChangeIso S.toSpecΓ f e

/-- Naturality for global-function matrices uses the actual coefficient pullback. -/
lemma globalLinearActionTwistBaseChangeIso_naturality {S T : Scheme.{u}} (n : ℕ) (f : T ⟶ S)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    globalLinearActionTwistBaseChangeIso n f e =
      Langlands.Scheme.Modules.squarePullbackIso
          (RelativeProjectiveSpace.map n f) (RelativeProjectiveSpace.map n f)
          (RelativeProjectiveSpace.globalLinearAction n (RelativeProjectiveSpace.coordinatePullback n f e))
          (RelativeProjectiveSpace.globalLinearAction n e)
          (RelativeProjectiveSpace.map_globalLinearAction n f e)
          (RelativeProjectiveSpace.twistOne S n).obj ≪≫
        (Scheme.Modules.pullback
          (RelativeProjectiveSpace.globalLinearAction n (RelativeProjectiveSpace.coordinatePullback n f e))).mapIso
          ((LineBundle.forget _).mapIso (RelativeProjectiveSpace.twistOnePullbackIso n f)) ≪≫
        globalLinearActionTwistIso T n (RelativeProjectiveSpace.coordinatePullback n f e) := by
  exact relativeLinearActionTwistBaseChangeIso_naturality S.toSpecΓ T.toSpecΓ f f.appTop.hom
    (Scheme.toSpecΓ_naturality f).symm e (RelativeProjectiveSpace.coordinatePullback n f e)
    (fun i j ↦ (RelativeProjectiveSpace.coordinatePullback_coeff n f e i j).symm)

end Langlands.AlgebraicGeometry.LinearSystem
