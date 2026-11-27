import Langlands.AlgebraicGeometry.AffineCechDeRham
import Langlands.AlgebraicGeometry.CechPullback

/-! # Pullback of functions and forms on compatible Čech covers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {h : Z ⟶ Spec (CommRingCat.of R)}

/-- The actual ring pullback for two compatible opens is an algebra map over the base. -/
def sectionAlgHomOver (a : X ⟶ Y) (ha : a ≫ g = f)
    {V : Y.Opens} {W : X.Opens} (e : W ≤ a ⁻¹ᵁ V) :
    (sectionAlgebras g).obj (op V) →ₐ[R] (sectionAlgebras f).obj (op W) :=
  { (a.appLE V W e).hom with
    commutes' := fun r => by
      change (g.appLE ⊤ V le_top ≫ a.appLE V W e).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE, ha] }

lemma sectionAlgHomOver_comp (a : X ⟶ Y) (ha : a ≫ g = f)
    (b : Y ⟶ Z) (hb : b ≫ h = g) {V : Z.Opens} {W : Y.Opens} {T : X.Opens}
    (hbV : W ≤ b ⁻¹ᵁ V) (haW : T ≤ a ⁻¹ᵁ W) :
    (sectionAlgHomOver a ha haW).comp (sectionAlgHomOver b hb hbV) =
      sectionAlgHomOver (a ≫ b) (by rw [Category.assoc, hb, ha])
        (haW.trans (a.preimage_mono hbV)) := by
  ext x
  change (b.appLE V W hbV ≫ a.appLE W T haW).hom x = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma sectionAlgHomOver_id (V : X.Opens) :
    sectionAlgHomOver (𝟙 X) (Category.id_comp f) (W := V) (V := V) le_rfl =
      AlgHom.id R ((sectionAlgebras f).obj (op V)) := by
  ext x
  change Γ(X, V) at x
  change (X.presheaf.map (𝟙 _)).hom x = x
  rw [X.presheaf.map_id]
  rfl

variable {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  (a : X ⟶ Y) (ha : a ≫ g = f) (α : U.I₀ → V.I₀)
  (hα : ∀ j, coverOpens U j ≤ a ⁻¹ᵁ coverOpens V (α j))

/-- The actual algebra map on a tuple intersection of compatible affine covers. -/
abbrev tupleAlgHomOver {p : ℕ} (σ : Fin (p + 1) → U.I₀) :=
  sectionAlgHomOver a ha (Cech.inter_le_preimage a hα σ)

private def tuplePullback {P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {Q : (Opens Y)ᵒᵖ ⥤ ModuleCat.{u} R} (p : ℕ)
    (τ : ∀ σ : Fin (p + 1) → U.I₀,
      Q.obj (op (inter (coverOpens V) (α ∘ σ))) →ₗ[R] P.obj (op (inter (coverOpens U) σ))) :
    Cochains V Q p →ₗ[R] Cochains U P p :=
  LinearMap.pi fun σ => (τ σ).comp (LinearMap.proj (α ∘ σ))

/-- Pullback of Čech function cochains. -/
def pullFunctions (p : ℕ) : Cochains V (functions g) p →ₗ[R] Cochains U (functions f) p :=
  tuplePullback α p fun σ => (tupleAlgHomOver a ha α hα σ).toLinearMap

/-- Pullback of Čech one-form cochains. -/
def pullOneForms (p : ℕ) : Cochains V (oneForms g) p →ₗ[R] Cochains U (oneForms f) p :=
  tuplePullback α p fun σ => by
    change Ω[((sectionAlgebras g).obj (op (inter (coverOpens V) (α ∘ σ))))⁄R] →ₗ[R]
      Ω[((sectionAlgebras f).obj (op (inter (coverOpens U) σ)))⁄R]
    let r := tupleAlgHomOver a ha α hα σ
    exact restrictBase R r (RelativeForms.mapOne r)

/-- Pullback of Čech two-form cochains. -/
def pullTwoForms (p : ℕ) : Cochains V (twoForms g) p →ₗ[R] Cochains U (twoForms f) p :=
  tuplePullback α p fun σ => by
    change RelativeForms.Two R ((sectionAlgebras g).obj (op (inter (coverOpens V) (α ∘ σ)))) →ₗ[R]
      RelativeForms.Two R ((sectionAlgebras f).obj (op (inter (coverOpens U) σ)))
    let r := tupleAlgHomOver a ha α hα σ
    exact restrictBase R r (RelativeForms.mapTwo r)

lemma pullFunctions_apply (p : ℕ) (c : Cochains V (functions g) p) (σ) :
    pullFunctions a ha α hα p c σ = tupleAlgHomOver a ha α hα σ (c (α ∘ σ)) := rfl

lemma pullOneForms_apply (p : ℕ) (c : Cochains V (oneForms g) p) (σ) :
    pullOneForms a ha α hα p c σ =
      RelativeForms.mapOne (tupleAlgHomOver a ha α hα σ) (c (α ∘ σ)) := rfl

lemma pullTwoForms_apply (p : ℕ) (c : Cochains V (twoForms g) p) (σ) :
    pullTwoForms a ha α hα p c σ =
      RelativeForms.mapTwo (tupleAlgHomOver a ha α hα σ) (c (α ∘ σ)) := rfl

lemma cechD_pullFunctions (p : ℕ) (c : Cochains V (functions g) p) :
    cechD U (functions f) p (pullFunctions a ha α hα p c) =
      pullFunctions a ha α hα (p + 1) (cechD V (functions g) p c) :=
  Cech.d_pull a hα p c

private lemma restrict_comp_tupleAlgHomOver {p : ℕ} (τ : Fin (p + 2) → U.I₀)
    (j : Fin (p + 2)) :
    (((sectionAlgebras f).map (homOfLE (inter_le_comp τ j.succAbove)).op).hom).comp
      (tupleAlgHomOver a ha α hα (τ ∘ j.succAbove)) =
    (tupleAlgHomOver a ha α hα τ).comp
      ((sectionAlgebras g).map (homOfLE (inter_le_comp (α ∘ τ) j.succAbove)).op).hom := by
  ext x
  change (a.appLE _ _ _ ≫ X.presheaf.map (homOfLE (inter_le_comp τ j.succAbove)).op).hom x =
    (Y.presheaf.map (homOfLE (inter_le_comp (α ∘ τ) j.succAbove)).op ≫ a.appLE _ _ _).hom x
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

set_option maxHeartbeats 800000 in
lemma cechD_pullOneForms (p : ℕ) (c : Cochains V (oneForms g) p) :
    cechD U (oneForms f) p (pullOneForms a ha α hα p c) =
      pullOneForms a ha α hα (p + 1) (cechD V (oneForms g) p c) := by
  funext τ
  rw [cechD_apply, pullOneForms_apply, cechD_apply, map_sum]
  simp only [pullOneForms_apply, map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·)
  let r₁ := tupleAlgHomOver a ha α hα (τ ∘ j.succAbove)
  let r₂ := ((sectionAlgebras f).map
    (homOfLE (inter_le_comp (U := coverOpens U) τ j.succAbove)).op).hom
  let s₁ := ((sectionAlgebras g).map
    (homOfLE (inter_le_comp (U := coverOpens V) (α ∘ τ) j.succAbove)).op).hom
  let s₂ := tupleAlgHomOver a ha α hα τ
  let x := c ((α ∘ τ) ∘ j.succAbove)
  change RelativeForms.mapOne r₂ (RelativeForms.mapOne r₁ x) =
    RelativeForms.mapOne s₂ (RelativeForms.mapOne s₁ x)
  calc
    _ = RelativeForms.mapOne (r₂.comp r₁) x := (RelativeForms.mapOne_comp r₁ r₂ x).symm
    _ = RelativeForms.mapOne (s₂.comp s₁) x :=
      congrArg (fun r => RelativeForms.mapOne r x) (restrict_comp_tupleAlgHomOver a ha α hα τ j)
    _ = _ := RelativeForms.mapOne_comp s₁ s₂ x

lemma pullOneForms_exteriorD0 (p : ℕ) (c : Cochains V (functions g) p) :
    pullOneForms a ha α hα p (cochainMap V (exteriorD0 g) p c) =
      cochainMap U (exteriorD0 f) p (pullFunctions a ha α hα p c) := by
  funext σ
  exact RelativeForms.mapOne_d (tupleAlgHomOver a ha α hα σ) (c (α ∘ σ))

lemma pullTwoForms_exteriorD1 (p : ℕ) (c : Cochains V (oneForms g) p) :
    pullTwoForms a ha α hα p (cochainMap V (exteriorD1 g) p c) =
      cochainMap U (exteriorD1 f) p (pullOneForms a ha α hα p c) := by
  funext σ
  exact (RelativeForms.dOne_natural (tupleAlgHomOver a ha α hα σ) (c (α ∘ σ))).symm

end Langlands.AlgebraicGeometry.AffineCechDeRham
