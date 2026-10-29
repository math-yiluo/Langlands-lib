import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Extending compatible norms from affine opens -/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.AffineNormGluing

variable {X Y : Scheme.{u}}

/-- Restriction as a ring homomorphism. -/
abbrev res (X : Scheme.{u}) {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
lemma res_res (X : Scheme.{u}) {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Γ(X, W)) : res X hUV (res X hVW s) = res X (hUV.trans hVW) s := by
  change (X.presheaf.map (homOfLE hUV).op) ((X.presheaf.map (homOfLE hVW).op) s) = _
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Sections are determined by their restrictions to all contained affine opens. -/
lemma affine_ext {U : X.Opens} (s t : Γ(X, U))
    (h : ∀ (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U),
      res X hVU s = res X hVU t) : s = t := by
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨V, hVU, hxV, h ⟨V, hV⟩ hVU⟩

/-- All affine opens contained in an arbitrary open cover that open. -/
lemma affine_cover (U : X.Opens) :
    U ≤ ⨆ V : {V : X.affineOpens // (V : X.Opens) ≤ U}, (V.1 : X.Opens) := by
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩

variable (π : Y ⟶ X)
  (N : ∀ V : X.affineOpens, Γ(Y, π ⁻¹ᵁ (V : X.Opens)) →* Γ(X, (V : X.Opens)))
  (hN : ∀ (U V : X.affineOpens) (hUV : (U : X.Opens) ≤ (V : X.Opens))
    (f : Γ(Y, π ⁻¹ᵁ (V : X.Opens))),
    res X hUV (N V f) = N U (res Y (Scheme.Hom.preimage_mono π hUV) f))

include hN in
/-- The affine norms of the restrictions of one section form a matching family. -/
lemma compatible (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)) :
    TopCat.Presheaf.IsCompatible X.presheaf
      (fun V : {V : X.affineOpens // (V : X.Opens) ≤ U} ↦ (V.1 : X.Opens))
      (fun V ↦ N V.1 (res Y (Scheme.Hom.preimage_mono π V.2) f)) := by
  intro V W
  apply affine_ext
  intro T hT
  change res X hT (res X inf_le_left (N V.1 _)) =
    res X hT (res X inf_le_right (N W.1 _))
  rw [res_res, res_res, hN, hN, res_res, res_res]

include hN in
/-- A compatible affine family glues uniquely over every open. -/
lemma existsUnique_norm (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)) :
    ∃! s : Γ(X, U), ∀ (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U),
      res X hVU s = N V (res Y (Scheme.Hom.preimage_mono π hVU) f) := by
  obtain ⟨s, hs, hu⟩ := X.sheaf.existsUnique_gluing'
    (fun V : {V : X.affineOpens // (V : X.Opens) ≤ U} ↦ (V.1 : X.Opens)) U
    (fun V ↦ homOfLE V.2) (affine_cover U)
    (fun V ↦ N V.1 (res Y (Scheme.Hom.preimage_mono π V.2) f))
    (compatible π N hN U f)
  exact ⟨s, fun V hV ↦ hs ⟨V, hV⟩, fun t ht ↦ hu t (fun V ↦ ht V.1 V.2)⟩

/-- The section obtained by gluing the affine norms. -/
def normSection (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)) : Γ(X, U) :=
  Classical.choose (existsUnique_norm π N hN U f)

lemma res_normSection (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U))
    (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U) :
    res X hVU (normSection π N hN U f) =
      N V (res Y (Scheme.Hom.preimage_mono π hVU) f) :=
  (Classical.choose_spec (existsUnique_norm π N hN U f)).1 V hVU

/-- The glued norm is multiplicative on every open. -/
def norm (U : X.Opens) : Γ(Y, π ⁻¹ᵁ U) →* Γ(X, U) where
  toFun := normSection π N hN U
  map_one' := by
    apply affine_ext
    intro V hV
    rw [res_normSection, map_one, map_one, map_one]
  map_mul' f g := by
    apply affine_ext
    intro V hV
    rw [res_normSection, map_mul, map_mul, map_mul, res_normSection, res_normSection]

lemma res_norm (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U))
    (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U) :
    res X hVU (norm π N hN U f) =
      N V (res Y (Scheme.Hom.preimage_mono π hVU) f) :=
  res_normSection π N hN U f V hVU

/-- The glued norms commute with all restrictions. -/
lemma naturality (U V : X.Opens) (hUV : U ≤ V) (f : Γ(Y, π ⁻¹ᵁ V)) :
    res X hUV (norm π N hN V f) =
      norm π N hN U (res Y (Scheme.Hom.preimage_mono π hUV) f) := by
  apply affine_ext
  intro W hW
  rw [res_res, res_norm, res_norm, res_res]

/-- The degree law on affine opens extends to every open. -/
lemma degree (d : ℕ)
    (hd : ∀ (V : X.affineOpens) (g : Γ(X, (V : X.Opens))),
      N V (π.app (V : X.Opens) g) = g ^ d)
    (U : X.Opens) (g : Γ(X, U)) : norm π N hN U (π.app U g) = g ^ d := by
  apply affine_ext
  intro V hV
  rw [res_norm, map_pow]
  have h := ConcreteCategory.congr_hom (π.naturality (homOfLE hV).op) g
  change (π.app (V : X.Opens)) (res X hV g) =
    res Y (Scheme.Hom.preimage_mono π hV) (π.app U g) at h
  rw [← h]
  exact hd V (res X hV g)

/-- A section and its restriction have the same nonvanishing at a point of the smaller open. -/
lemma mem_basicOpen_res {U V : X.Opens} (hUV : U ≤ V) (f : Γ(X, V))
    (x : X) (hx : x ∈ U) : x ∈ X.basicOpen (res X hUV f) ↔ x ∈ X.basicOpen f := by
  change x ∈ X.basicOpen (X.presheaf.map (homOfLE hUV).op f) ↔ _
  rw [Scheme.basicOpen_res]
  exact and_iff_right hx

/-- The two-sided fibre nonvanishing equality extends from affine opens to all opens. -/
lemma basicOpen (hB : ∀ (V : X.affineOpens) (f : Γ(Y, π ⁻¹ᵁ (V : X.Opens))),
    (X.basicOpen (N V f) : Set X) =
      {x : X | x ∈ (V : X.Opens) ∧ ∀ y : Y, π.base y = x → y ∈ Y.basicOpen f})
    (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)) :
    (X.basicOpen (norm π N hN U f) : Set X) =
      {x : X | x ∈ U ∧ ∀ y : Y, π.base y = x → y ∈ Y.basicOpen f} := by
  ext x
  constructor
  · intro hx
    have hxU : x ∈ U := X.basicOpen_le _ hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    change V ∈ X.affineOpens at hV
    have hx' : x ∈ X.basicOpen
        (N ⟨V, hV⟩ (res Y (Scheme.Hom.preimage_mono π hVU) f)) := by
      rw [← res_norm π N hN U f ⟨V, hV⟩ hVU]
      exact (mem_basicOpen_res hVU _ x hxV).mpr hx
    change x ∈ (X.basicOpen (N ⟨V, hV⟩
      (res Y (Scheme.Hom.preimage_mono π hVU) f)) : Set X) at hx'
    rw [hB] at hx'
    refine ⟨hxU, fun y hy ↦ ?_⟩
    exact (mem_basicOpen_res (Scheme.Hom.preimage_mono π hVU) f y
      (by change π.base y ∈ V; rw [hy]; exact hxV)).mp (hx'.2 y hy)
  · rintro ⟨hxU, hf⟩
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    change V ∈ X.affineOpens at hV
    have hx' : x ∈ X.basicOpen
        (N ⟨V, hV⟩ (res Y (Scheme.Hom.preimage_mono π hVU) f)) := by
      change x ∈ (X.basicOpen (N ⟨V, hV⟩
        (res Y (Scheme.Hom.preimage_mono π hVU) f)) : Set X)
      rw [hB]
      refine ⟨hxV, fun y hy ↦ ?_⟩
      exact (mem_basicOpen_res (Scheme.Hom.preimage_mono π hVU) f y
        (by change π.base y ∈ V; rw [hy]; exact hxV)).mpr (hf y hy)
    rw [← res_norm π N hN U f ⟨V, hV⟩ hVU] at hx'
    exact (mem_basicOpen_res hVU _ x hxV).mp hx'

end Langlands.AlgebraicGeometry.Picard.AffineNormGluing
