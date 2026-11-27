import Langlands.AlgebraicGeometry.AffineCechDeRhamSchemePullback

/-! # Section pullbacks of locally lifted scheme morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_apply inter_le_comp)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}

private lemma openInclusion_appLE_self (W : X.Opens) :
    W.ι.appLE W ⊤ (by rw [Scheme.Opens.ι_preimage_self]) = W.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv, eqToHom_op]
  rfl

private lemma openInclusion_restrictTop {W W' : X.Opens} (e : W' ≤ W) :
    (X.homOfLE e).appTop ≫ W'.topIso.hom = W.topIso.hom ≫ X.presheaf.map (homOfLE e).op := by
  have h := (arrowResLEAppIso (𝟙 X) W W' (by simpa using e)).hom.w.symm
  change (Scheme.Hom.resLE (𝟙 X) W W' _).appTop ≫ W'.topIso.hom =
    W.topIso.hom ≫ Scheme.Hom.appLE (𝟙 X) W W' _ at h
  simpa only [Scheme.Hom.resLE_id, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using h

private lemma appTop_eq_appLE (a : X ⟶ Y) : a.appTop = a.appLE ⊤ ⊤ le_top :=
  a.app_eq_appLE

private lemma appLE_congr_morphism {a b : X ⟶ Y} (h : a = b)
    (T : Y.Opens) (W : X.Opens) (ea : W ≤ a ⁻¹ᵁ T) (eb : W ≤ b ⁻¹ᵁ T) :
    a.appLE T W ea = b.appLE T W eb := by
  subst b
  rfl

/-- Pullback to an open subscheme by a morphism defined on that subscheme. -/
def pullbackSectionsFromOpen {W : X.Opens} (γ : W.toScheme ⟶ Y)
    (hγ : γ ≫ g = W.ι ≫ f) {Z : Y.Opens} (e : ⊤ ≤ γ ⁻¹ᵁ Z) :
    (sectionAlgebras g).obj (op Z) →ₐ[R] (sectionAlgebras f).obj (op W) :=
  { (γ.appLE Z ⊤ e ≫ W.topIso.hom).hom with
    commutes' := fun r => by
      change (g.appLE ⊤ Z le_top ≫ γ.appLE Z ⊤ e ≫ W.topIso.hom).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, hγ,
        ← Scheme.Hom.appLE_comp_appLE W.ι f ⊤ W ⊤ le_top
          (by rw [Scheme.Opens.ι_preimage_self]), Category.assoc,
        openInclusion_appLE_self, Iso.inv_hom_id, Category.comp_id] }

section LocalMorphisms

variable {Z : Scheme.{u}} (r : Z ⟶ X) [Surjective r] (m : Z ⟶ Y)
  (β : U.I₀ → V.I₀)
  (ℓ : ∀ i, (coverOpens U i).toScheme ⟶ Y)
  (hℓ : ∀ i, ℓ i ≫ g = (coverOpens U i).ι ≫ f)
  (hred : ∀ i, r.resLE (coverOpens U i) (r ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ i =
    (r ⁻¹ᵁ coverOpens U i).ι ≫ m)
  (hβ : ∀ i, r ⁻¹ᵁ coverOpens U i ≤ m ⁻¹ᵁ coverOpens V (β i))

private abbrev chartMap {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    (inter (coverOpens U) σ).toScheme ⟶ Y :=
  X.homOfLE (inter_le_apply σ i) ≫ ℓ (σ i)

include hℓ in
private lemma chartMap_over {p : ℕ} (σ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    chartMap ℓ σ i ≫ g = (inter (coverOpens U) σ).ι ≫ f := by
  rw [Category.assoc, hℓ, ← Category.assoc, Scheme.homOfLE_ι]

private lemma chartMap_restrict {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)) :
    X.homOfLE (inter_le_comp τ θ) ≫ chartMap ℓ (τ ∘ θ) i = chartMap ℓ τ (θ i) := by
  rw [← Category.assoc, Scheme.homOfLE_homOfLE]
  rfl

omit [Surjective r] in
include hred in
private lemma chartMap_reduces {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    r.resLE (inter (coverOpens U) τ) (r ⁻¹ᵁ inter (coverOpens U) τ) le_rfl ≫ chartMap ℓ τ i =
      (r ⁻¹ᵁ inter (coverOpens U) τ).ι ≫ m := by
  let W := inter (coverOpens U) τ
  let A := coverOpens U (τ i)
  let hWA : W ≤ A := inter_le_apply τ i
  let hrWA : r ⁻¹ᵁ W ≤ r ⁻¹ᵁ A := r.preimage_mono hWA
  have hr : r.resLE W (r ⁻¹ᵁ W) le_rfl ≫ X.homOfLE hWA =
      Z.homOfLE hrWA ≫ r.resLE A (r ⁻¹ᵁ A) le_rfl := by
    rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]
  change r.resLE W (r ⁻¹ᵁ W) le_rfl ≫ X.homOfLE hWA ≫ ℓ (τ i) = (r ⁻¹ᵁ W).ι ≫ m
  rw [← Category.assoc, hr, Category.assoc, hred, ← Category.assoc, Scheme.homOfLE_ι]

private lemma resLE_preimage_surjective (W : X.Opens) :
    Function.Surjective (r.resLE W (r ⁻¹ᵁ W) le_rfl) := by
  intro x
  obtain ⟨z, hz⟩ := r.surjective x.val
  let y : (r ⁻¹ᵁ W).toScheme := ⟨z, by change r z ∈ W; rw [hz]; exact x.property⟩
  exact ⟨y, Subtype.ext ((Scheme.Hom.coe_resLE_apply r le_rfl y).trans hz)⟩

include hred hβ in
private lemma chartMap_into {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    ⊤ ≤ chartMap ℓ τ i ⁻¹ᵁ inter (coverOpens V) (β ∘ τ) := by
  intro x _
  obtain ⟨z, rfl⟩ := resLE_preimage_surjective r (inter (coverOpens U) τ) x
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, chartMap_reduces r m ℓ hred]
  rw [Langlands.Cohomology.Cech.mem_inter]
  exact fun j => hβ (τ j) ((r.preimage_mono (inter_le_apply τ j)) z.property)

private abbrev chartSections {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    tupleSections g V (β ∘ τ) →ₐ[R] tupleSections f U τ :=
  pullbackSectionsFromOpen (chartMap ℓ τ i) (chartMap_over ℓ hℓ τ i)
    (chartMap_into r m β ℓ hred hβ τ i)

private lemma restrict_chartSections {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)) :
    (restrictSections f U τ θ).comp (chartSections r m β ℓ hℓ hred hβ (τ ∘ θ) i) =
      (chartSections r m β ℓ hℓ hred hβ τ (θ i)).comp (restrictSections g V (β ∘ τ) θ) := by
  let W := inter (coverOpens U) τ
  let W' := inter (coverOpens U) (τ ∘ θ)
  let T := inter (coverOpens V) (β ∘ τ)
  let T' := inter (coverOpens V) (β ∘ τ ∘ θ)
  let hW : W ≤ W' := inter_le_comp τ θ
  let hT : T ≤ T' := inter_le_comp (β ∘ τ) θ
  have htop : ⊤ ≤ chartMap ℓ τ (θ i) ⁻¹ᵁ T' :=
    (chartMap_into r m β ℓ hred hβ τ (θ i)).trans ((chartMap ℓ τ (θ i)).preimage_mono hT)
  ext a
  change ((chartMap ℓ (τ ∘ θ) i).appLE T' ⊤ _ ≫
      W'.topIso.hom ≫ X.presheaf.map (homOfLE hW).op).hom a =
    (Y.presheaf.map (homOfLE hT).op ≫
      (chartMap ℓ τ (θ i)).appLE T ⊤ _ ≫ W.topIso.hom).hom a
  rw [← openInclusion_restrictTop hW, ← Category.assoc, ← Category.assoc,
    appTop_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_morphism (chartMap_restrict ℓ τ θ i) T' ⊤ _ htop, Scheme.Hom.map_appLE]

private lemma reduced_chartSections {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1))
    (a : tupleSections g V (β ∘ τ)) :
    (r.appLE (inter (coverOpens U) τ) (r ⁻¹ᵁ inter (coverOpens U) τ) le_rfl).hom
        (chartSections r m β ℓ hℓ hred hβ τ i a) =
      (m.appLE (inter (coverOpens V) (β ∘ τ)) (r ⁻¹ᵁ inter (coverOpens U) τ)
        (fun x hx => (Langlands.Cohomology.Cech.mem_inter (β ∘ τ) (m x)).mpr
          (fun j => hβ (τ j) (r.preimage_mono (inter_le_apply τ j) hx)))).hom a := by
  let W := inter (coverOpens U) τ
  let W₀ := r ⁻¹ᵁ W
  let T := inter (coverOpens V) (β ∘ τ)
  let s := r.resLE W W₀ le_rfl
  have hT : W₀ ≤ m ⁻¹ᵁ T := fun x hx =>
    (Langlands.Cohomology.Cech.mem_inter (β ∘ τ) (m x)).mpr
      (fun j => hβ (τ j) (r.preimage_mono (inter_le_apply τ j) hx))
  have hW : ⊤ ≤ W₀.ι ⁻¹ᵁ W₀ := by rw [Scheme.Opens.ι_preimage_self]
  have htop : ⊤ ≤ (W₀.ι ≫ m) ⁻¹ᵁ T := hW.trans (W₀.ι.preimage_mono hT)
  have hs : s.appTop ≫ W₀.topIso.hom = W.topIso.hom ≫ r.appLE W W₀ le_rfl :=
    (arrowResLEAppIso r W W₀ le_rfl).hom.w.symm
  change ((chartMap ℓ τ i).appLE T ⊤ _ ≫ W.topIso.hom ≫ r.appLE W W₀ le_rfl).hom a = _
  rw [← hs, appTop_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_morphism (chartMap_reduces r m ℓ hred τ i) T ⊤ _ htop,
    ← Scheme.Hom.appLE_comp_appLE W₀.ι m T W₀ ⊤ hT hW, Category.assoc,
    openInclusion_appLE_self, Iso.inv_hom_id, Category.comp_id]

variable (I : Ideal R) [IsSeparated f]
  (hker : ∀ (W : X.Opens), IsAffineOpen W →
    RingHom.ker (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom =
      I.map (algebraMap R ((sectionAlgebras f).obj (op W))))

/-- Local morphisms of the thicker charts inducing a common morphism on the
reduction give the system of compatible affine pullbacks. -/
def LocalPullbacks.ofLocalMorphisms : LocalPullbacks (f := f) (g := g) I β where
  sections := chartSections r m β ℓ hℓ hred hβ
  restrict_sections := restrict_chartSections r m β ℓ hℓ hred hβ
  congruent := by
    intro p τ i j a
    rw [← hker _ (isAffineOpen_inter f U τ), RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (reduced_chartSections r m β ℓ hℓ hred hβ τ i a).trans
      (reduced_chartSections r m β ℓ hℓ hred hβ τ j a).symm

/-- Any two families lifting the same morphism have congruent section
pullbacks on each affine overlap. -/
lemma localMorphisms_congruent
    (ℓ' : ∀ i, (coverOpens U i).toScheme ⟶ Y)
    (hℓ' : ∀ i, ℓ' i ≫ g = (coverOpens U i).ι ≫ f)
    (hred' : ∀ i, r.resLE (coverOpens U i) (r ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ' i =
      (r ⁻¹ᵁ coverOpens U i).ι ≫ m)
    {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i j : Fin (p + 1))
    (a : tupleSections g V (β ∘ τ)) :
    (LocalPullbacks.ofLocalMorphisms r m β ℓ hℓ hred hβ I hker).sections τ i a -
      (LocalPullbacks.ofLocalMorphisms r m β ℓ' hℓ' hred' hβ I hker).sections τ j a ∈
        I.map (algebraMap R (tupleSections f U τ)) := by
  rw [← hker _ (isAffineOpen_inter f U τ), RingHom.mem_ker, map_sub, sub_eq_zero]
  exact (reduced_chartSections r m β ℓ hℓ hred hβ τ i a).trans
    (reduced_chartSections r m β ℓ' hℓ' hred' hβ τ j a).symm

variable (γ : X ⟶ Y) (hγ : γ ≫ g = f) (hγ₀ : r ≫ γ = m)
  (hγβ : ∀ i, coverOpens U i ≤ γ ⁻¹ᵁ coverOpens V (β i))

include hγ₀ in
/-- The section maps obtained from a global lift and from the local lifts
agree modulo the extended base ideal on every overlap. -/
lemma localMorphisms_congruent_global {p : ℕ} (τ : Fin (p + 1) → U.I₀)
    (i j : Fin (p + 1)) (a : tupleSections g V (β ∘ τ)) :
    (LocalPullbacks.ofLocalMorphisms r m β ℓ hℓ hred hβ I hker).sections τ i a -
      (LocalPullbacks.ofMorphism I γ hγ β hγβ).sections τ j a ∈
        I.map (algebraMap R (tupleSections f U τ)) := by
  rw [← hker _ (isAffineOpen_inter f U τ), RingHom.mem_ker, map_sub, sub_eq_zero]
  let W := inter (coverOpens U) τ
  let T := inter (coverOpens V) (β ∘ τ)
  have hW : r ⁻¹ᵁ W ≤ m ⁻¹ᵁ T := fun x hx =>
    (Langlands.Cohomology.Cech.mem_inter (β ∘ τ) (m x)).mpr
      (fun k => hβ (τ k) (r.preimage_mono (inter_le_apply τ k) hx))
  refine (reduced_chartSections r m β ℓ hℓ hred hβ τ i a).trans ?_
  symm
  change (γ.appLE T W _ ≫ r.appLE W (r ⁻¹ᵁ W) le_rfl).hom a =
    (m.appLE T (r ⁻¹ᵁ W) hW).hom a
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_morphism hγ₀ T (r ⁻¹ᵁ W) _ hW]

end LocalMorphisms

end Langlands.AlgebraicGeometry.AffineCechDeRham
