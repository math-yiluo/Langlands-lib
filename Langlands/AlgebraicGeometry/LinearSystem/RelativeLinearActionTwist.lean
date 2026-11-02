import Langlands.AlgebraicGeometry.LinearSystem.CoefficientComparison
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.GlobalLinearAction

/-! # The degree-one twist under relative projective linear actions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality transport followed by an isomorphism has the expected section formula. -/
lemma pullbackCongr_trans_coordinate {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) {N : X.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ≅ N) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackCongr h).app M ≪≫ φ).hom.app ⊤
        (pullbackSection f M s) =
      φ.hom.app ⊤ (pullbackSection g M s) := by
  simp only [Iso.trans_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [pullbackCongr_coordinate]

/-- Transport an actual section-preserving isomorphism together with its coordinate law. -/
def pullbackCongrCoordinateIso {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) {N : X.Modules} {ι : Type*}
    (s : ι → GlobalSections M) (t : ι → GlobalSections N)
    (φ : (Scheme.Modules.pullback g).obj M ≅ N)
    (hφ : ∀ i, φ.hom.app ⊤ (pullbackSection g M (s i)) = t i) :
    {ψ : (Scheme.Modules.pullback f).obj M ≅ N //
      ∀ i, ψ.hom.app ⊤ (pullbackSection f M (s i)) = t i} :=
  ⟨(Scheme.Modules.pullbackCongr h).app M ≪≫ φ,
    fun i ↦ (pullbackCongr_trans_coordinate h M φ (s i)).trans (hφ i)⟩

/-- A section-preserving comparison over an identity morphism is canonical. -/
lemma pullback_comparison_refl {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (f : X ⟶ X) (w : f = 𝟙 X) (α : (Scheme.Modules.pullback f).obj M ≅ M)
    (hα : ∀ i, α.hom.app ⊤ (pullbackSection f M (s i)) = s i) :
    α = (Scheme.Modules.pullbackCongr w).app M ≪≫ (Scheme.Modules.pullbackId X).app M := by
  apply Iso.ext
  apply hom_ext_of_generating_sections _ (frameCover_pullback hM s hs f)
  intro i
  exact (hα i).trans
    ((pullbackCongr_trans_coordinate w M ((Scheme.Modules.pullbackId X).app M) (s i)).trans
      (pullbackId_coordinate M (s i))).symm

/-- A section comparison over the coefficient base commutes with linear combinations. -/
lemma pullback_comparison_linearChange {K : Type u} [CommRing K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) {L M : LineBundle X} {n : ℕ}
    (s : Fin (n + 1) → GlobalSections L.obj)
    (t : Fin (n + 1) → GlobalSections M.obj) (g : X ⟶ X) (hg : g ≫ p = p)
    (φ : (Scheme.Modules.pullback g).obj L.obj ⟶ M.obj)
    (hφ : ∀ i, φ.app ⊤ (pullbackSection g L.obj (s i)) = t i)
    (f : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K)) (i : Fin (n + 1)) :
    φ.app ⊤ (pullbackSection g L.obj (linearChangeSections p s f i)) =
      linearChangeSections p t f i := by
  have hc (r : K) : g.appTop (Scheme.Modules.scalarsFromBase p r) =
      Scheme.Modules.scalarsFromBase p r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫ g.appTop) r = _
    rw [← Scheme.Hom.comp_appTop, hg]
    rfl
  simp only [linearChangeSections, linComb, pullbackSection_sum, pullbackSection_smul,
    map_sum, Scheme.Modules.Hom.app_smul, hc, hφ]

/-- Linear coordinate formulas imply the canonical composition law for comparisons. -/
lemma linearChange_pullback_comparison_comp {K : Type u} [CommRing K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) {L : LineBundle X} {n : ℕ}
    (s : Fin (n + 1) → GlobalSections L.obj)
    (hs : (⨆ i, trivializationOpen L.obj (s i)) = ⊤)
    (a b c : X ⟶ X) (w : a ≫ b = c) (ha : a ≫ p = p)
    (e f : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (α : (Scheme.Modules.pullback a).obj L.obj ⟶ L.obj)
    (β : (Scheme.Modules.pullback b).obj L.obj ⟶ L.obj)
    (γ : (Scheme.Modules.pullback c).obj L.obj ⟶ L.obj)
    (hα : ∀ i, α.app ⊤ (pullbackSection a L.obj (s i)) =
      linearChangeSections p s e.toLinearMap i)
    (hβ : ∀ i, β.app ⊤ (pullbackSection b L.obj (s i)) =
      linearChangeSections p s f.toLinearMap i)
    (hγ : ∀ i, γ.app ⊤ (pullbackSection c L.obj (s i)) =
      linearChangeSections p s (e.trans f).toLinearMap i) :
    (Scheme.Modules.pullback a).map β ≫ α =
      (Scheme.Modules.pullbackComp a b).hom.app L.obj ≫
        (Scheme.Modules.pullbackCongr w).hom.app L.obj ≫ γ := by
  apply pullback_comparison_comp L.property s hs a b c w
  intro i
  rw [hβ, hγ]
  rw [pullback_comparison_linearChange (L := L) (M := L) p s
    (linearChangeSections p s e.toLinearMap) a ha α hα]
  exact congrFun (linearChangeSections_comp p s e.toLinearMap f.toLinearMap) i

variable {K : Type u} [CommRing K] {S : Scheme.{u}} {n : ℕ}
  (a : S ⟶ Spec (CommRingCat.of K))
  (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))

/-- The relative coordinate sections recover the actual polynomial projection. -/
lemma linearSystemMap_relativeProjectiveCoordinates :
    linearSystemMap (RelativeProjectiveSpace.toBase S n ≫ a)
        (relativeProjectiveCoordinates_generate S n) =
      RelativeProjectiveSpace.toPolynomial n a := by
  rw [← relativeLinearSystemMap_toPolynomial,
    relativeLinearSystemMap_relativeProjectiveCoordinates, Category.id_comp]

/-- The actual relative coordinates transformed by an invertible coefficient map. -/
def changedRelativeProjectiveCoordinates :
    Fin (n + 1) → GlobalSections (RelativeProjectiveSpace.twistOne S n).obj :=
  linearChangeSections (L := RelativeProjectiveSpace.twistOne S n)
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n) e.toLinearMap

/-- An invertible transformation preserves generation by the relative coordinates. -/
lemma changedRelativeProjectiveCoordinates_generate :
    ∀ x : RelativeProjectiveSpace S n, ∃ i,
      x ∈ nonvanishingLocus (RelativeProjectiveSpace.twistOne S n).obj
        (changedRelativeProjectiveCoordinates a e i) :=
  linearChangeSections_generate (L := RelativeProjectiveSpace.twistOne S n)
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n) e
    (relativeProjectiveCoordinates_generate S n)

/-- The changed relative coordinates define the existing relative linear action. -/
lemma relativeLinearSystemMap_changedRelativeProjectiveCoordinates :
    relativeLinearSystemMap (RelativeProjectiveSpace.toBase S n)
        (changedRelativeProjectiveCoordinates_generate a e) =
      RelativeProjectiveSpace.linearAction a e := by
  apply RelativeProjectiveSpace.hom_ext_toPolynomial a
  · simp
  · rw [relativeLinearSystemMap_toPolynomial,
      RelativeProjectiveSpace.linearAction_toPolynomial]
    have h := linearSystemMap_linearChange (L := RelativeProjectiveSpace.twistOne S n)
      (RelativeProjectiveSpace.toBase S n ≫ a)
      (RelativeProjectiveSpace.twistOneCoordinate S n) e
      (relativeProjectiveCoordinates_generate S n)
    rw [linearSystemMap_relativeProjectiveCoordinates] at h
    exact h.symm

/-- The actual relative action comparison, packaged with its coordinate law. -/
def relativeLinearActionTwistData :
    {φ : (Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction a e)).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅
        (RelativeProjectiveSpace.twistOne S n).obj //
      ∀ i, φ.hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.linearAction a e)
          (RelativeProjectiveSpace.twistOne S n).obj
          (RelativeProjectiveSpace.twistOneCoordinate S n i)) =
        changedRelativeProjectiveCoordinates a e i} :=
  pullbackCongrCoordinateIso
    (relativeLinearSystemMap_changedRelativeProjectiveCoordinates a e).symm
    (RelativeProjectiveSpace.twistOne S n).obj
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (changedRelativeProjectiveCoordinates a e)
    (relativeLinearSystemTwistIso (L := RelativeProjectiveSpace.twistOne S n)
      (changedRelativeProjectiveCoordinates a e) (RelativeProjectiveSpace.toBase S n)
      (changedRelativeProjectiveCoordinates_generate a e))
    (relativeLinearSystemTwistIso_coordinate (L := RelativeProjectiveSpace.twistOne S n)
      (changedRelativeProjectiveCoordinates a e) (RelativeProjectiveSpace.toBase S n)
      (changedRelativeProjectiveCoordinates_generate a e))

/-- The actual pullback of the relative degree-one twist under a linear action. -/
def relativeLinearActionTwistIso :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction a e)).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅
      (RelativeProjectiveSpace.twistOne S n).obj :=
  (relativeLinearActionTwistData a e).val

/-- The comparison sends each pulled-back coordinate to its actual linear combination. -/
lemma relativeLinearActionTwistIso_coordinate (i : Fin (n + 1)) :
    (relativeLinearActionTwistIso a e).hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.linearAction a e)
          (RelativeProjectiveSpace.twistOne S n).obj
          (RelativeProjectiveSpace.twistOneCoordinate S n i)) =
      changedRelativeProjectiveCoordinates a e i :=
  (relativeLinearActionTwistData a e).property i

/-- At the identity coefficient map, the comparison is the canonical identity pullback. -/
lemma relativeLinearActionTwistIso_refl :
    relativeLinearActionTwistIso (n := n) a (LinearEquiv.refl K _) =
      (Scheme.Modules.pullbackCongr (RelativeProjectiveSpace.linearAction_refl a)).app
          (RelativeProjectiveSpace.twistOne S n).obj ≪≫
        (Scheme.Modules.pullbackId (RelativeProjectiveSpace S n)).app
          (RelativeProjectiveSpace.twistOne S n).obj := by
  apply pullback_comparison_refl (RelativeProjectiveSpace.twistOne S n).property
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (isOpenCover_trivializationOpen (L := RelativeProjectiveSpace.twistOne S n)
      (relativeProjectiveCoordinates_generate S n))
  intro i
  rw [relativeLinearActionTwistIso_coordinate]
  exact congrFun (linearChangeSections_id (L := RelativeProjectiveSpace.twistOne S n)
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n)) i

/-- The comparison commutes with every further linear combination of coordinates. -/
lemma relativeLinearActionTwistIso_linearChange
    (f : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K)) (i : Fin (n + 1)) :
    (relativeLinearActionTwistIso a e).hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.linearAction a e)
          (RelativeProjectiveSpace.twistOne S n).obj
          (linearChangeSections (L := RelativeProjectiveSpace.twistOne S n)
            (RelativeProjectiveSpace.toBase S n ≫ a)
            (RelativeProjectiveSpace.twistOneCoordinate S n) f i)) =
      linearChangeSections (L := RelativeProjectiveSpace.twistOne S n)
        (RelativeProjectiveSpace.toBase S n ≫ a)
        (changedRelativeProjectiveCoordinates a e) f i := by
  exact pullback_comparison_linearChange (L := RelativeProjectiveSpace.twistOne S n)
    (M := RelativeProjectiveSpace.twistOne S n) (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n) (changedRelativeProjectiveCoordinates a e)
    (RelativeProjectiveSpace.linearAction a e)
    (by rw [← Category.assoc, RelativeProjectiveSpace.linearAction_toBase])
    (relativeLinearActionTwistIso a e).hom (relativeLinearActionTwistIso_coordinate a e) f i

/-- The relative comparisons satisfy the canonical composition law for pullback. -/
lemma relativeLinearActionTwistIso_comp
    (f : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.linearAction a e)).map
        (relativeLinearActionTwistIso a f).hom ≫ (relativeLinearActionTwistIso a e).hom =
      (Scheme.Modules.pullbackComp (RelativeProjectiveSpace.linearAction a e)
        (RelativeProjectiveSpace.linearAction a f)).hom.app
        (RelativeProjectiveSpace.twistOne S n).obj ≫
      (Scheme.Modules.pullbackCongr
        (RelativeProjectiveSpace.linearAction_comp a e f)).hom.app
        (RelativeProjectiveSpace.twistOne S n).obj ≫
      (relativeLinearActionTwistIso a (e.trans f)).hom := by
  exact linearChange_pullback_comparison_comp (L := RelativeProjectiveSpace.twistOne S n)
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (isOpenCover_trivializationOpen (L := RelativeProjectiveSpace.twistOne S n)
      (relativeProjectiveCoordinates_generate S n))
    (RelativeProjectiveSpace.linearAction a e) (RelativeProjectiveSpace.linearAction a f)
    (RelativeProjectiveSpace.linearAction a (e.trans f))
    (RelativeProjectiveSpace.linearAction_comp a e f)
    (by rw [← Category.assoc, RelativeProjectiveSpace.linearAction_toBase]) e f
    (relativeLinearActionTwistIso a e).hom (relativeLinearActionTwistIso a f).hom
    (relativeLinearActionTwistIso a (e.trans f)).hom
    (relativeLinearActionTwistIso_coordinate a e)
    (relativeLinearActionTwistIso_coordinate a f)
    (relativeLinearActionTwistIso_coordinate a (e.trans f))

/-- Specialization to an invertible matrix of global functions on the base scheme. -/
abbrev globalLinearActionTwistIso
    (S : Scheme.{u}) (n : ℕ)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.globalLinearAction n e)).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅
      (RelativeProjectiveSpace.twistOne S n).obj :=
  relativeLinearActionTwistIso S.toSpecΓ e

end Langlands.AlgebraicGeometry.LinearSystem
