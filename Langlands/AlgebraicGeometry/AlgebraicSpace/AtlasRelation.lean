import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib

/-! # The equivalence relation of an atlas

For a natural transformation `a : Y(U) ⟶ F` with a represented kernel pair `R = U ×_F U`, the
two projections `t s : R ⟶ U` define an equivalence relation on `U` in the absolute sense used by
the statements of Stacks 03BM and 03JE: `(t, s)` is a monomorphism into `U × U` and its points
form an equivalence relation. The relation restricts to every open `W ⊆ U` with
`s⁻¹ W = t⁻¹ W`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation

/-- The absolute equivalence-relation hypotheses of `FiniteLocallyFreeEquivalenceRelation*`
for `t s : R ⟶ U`. -/
structure IsEquivRel {U R : Scheme.{u}} (t s : R ⟶ U) : Prop where
  mono : Mono (prod.lift t s)
  refl : ∀ (T : Scheme.{u}) (a : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a
  symm : ∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t
  trans : ∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
    ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s

section KernelPair

variable {S : Scheme.{u}} {F : Presheaf S} {U R : Over S}

/-- The projections of a kernel pair of a presheaf map from a scheme form an equivalence
relation on the underlying schemes. -/
theorem isEquivRel_of_isPullback (a : (schemeYoneda S).obj U ⟶ F) (t s : R ⟶ U)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a) :
    IsEquivRel t.left s.left := by
  let Y := schemeYoneda S
  have lift : ∀ {T : Over S} (a₁ a₂ : T ⟶ U), Y.map a₁ ≫ a = Y.map a₂ ≫ a →
      ∃ r : T ⟶ R, r ≫ t = a₁ ∧ r ≫ s = a₂ := by
    intro T a₁ a₂ w
    refine ⟨Y.preimage (h.lift (Y.map a₁) (Y.map a₂) w), ?_, ?_⟩
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, h.lift_fst]
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, h.lift_snd]
  have ext : ∀ {T : Over S} (r r' : T ⟶ R), r ≫ t = r' ≫ t → r ≫ s = r' ≫ s → r = r' := by
    intro T r r' h₁ h₂
    apply Y.map_injective
    apply h.hom_ext
    · rw [← Y.map_comp, ← Y.map_comp, h₁]
    · rw [← Y.map_comp, ← Y.map_comp, h₂]
  have hw : Y.map t ≫ a = Y.map s ≫ a := h.w
  have hRt : t.left ≫ U.hom = R.hom := Over.w t
  have hRs : s.left ≫ U.hom = R.hom := Over.w s
  refine ⟨⟨fun {T} g k hgk => ?_⟩, fun T a₀ => ?_, fun T r => ?_, fun T r r' hrr => ?_⟩
  · have h₁ : g ≫ t.left = k ≫ t.left := by simpa using congrArg (· ≫ prod.fst) hgk
    have h₂ : g ≫ s.left = k ≫ s.left := by simpa using congrArg (· ≫ prod.snd) hgk
    let T' : Over S := Over.mk (g ≫ R.hom)
    have hk : k ≫ R.hom = g ≫ R.hom := by
      calc k ≫ R.hom = k ≫ s.left ≫ U.hom := by rw [hRs]
        _ = g ≫ s.left ≫ U.hom := by rw [← Category.assoc, ← h₂, Category.assoc]
        _ = g ≫ R.hom := by rw [hRs]
    have := ext (T := T') (Over.homMk g) (Over.homMk k hk) (Over.OverMorphism.ext h₁)
      (Over.OverMorphism.ext h₂)
    exact congrArg CommaMorphism.left this
  · obtain ⟨r, hr₁, hr₂⟩ := lift (T := Over.mk (a₀ ≫ U.hom)) (Over.homMk a₀) (Over.homMk a₀) rfl
    exact ⟨r.left, congrArg CommaMorphism.left hr₁, congrArg CommaMorphism.left hr₂⟩
  · let T' : Over S := Over.mk (r ≫ R.hom)
    let rh : T' ⟶ R := Over.homMk r
    obtain ⟨r', hr₁, hr₂⟩ := lift (rh ≫ s) (rh ≫ t) (by
      rw [Y.map_comp, Y.map_comp, Category.assoc, Category.assoc, hw])
    exact ⟨r'.left, congrArg CommaMorphism.left hr₁, congrArg CommaMorphism.left hr₂⟩
  · let T' : Over S := Over.mk (r ≫ R.hom)
    let rh : T' ⟶ R := Over.homMk r
    have hr' : r' ≫ R.hom = r ≫ R.hom := by
      calc r' ≫ R.hom = r' ≫ t.left ≫ U.hom := by rw [hRt]
        _ = r ≫ s.left ≫ U.hom := by rw [← Category.assoc, ← hrr, Category.assoc]
        _ = r ≫ R.hom := by rw [hRs]
    let rh' : T' ⟶ R := Over.homMk r' hr'
    have hcomp : rh ≫ s = rh' ≫ t := Over.OverMorphism.ext hrr
    obtain ⟨r'', hr₁, hr₂⟩ := lift (rh ≫ t) (rh' ≫ s) (by
      rw [Y.map_comp, Y.map_comp, Category.assoc, Category.assoc, hw, ← Category.assoc,
        ← Y.map_comp, hcomp, Y.map_comp, Category.assoc, hw])
    exact ⟨r''.left, congrArg CommaMorphism.left hr₁, congrArg CommaMorphism.left hr₂⟩

/-- A representable map from a scheme has a represented kernel pair, and its projections form
an equivalence relation. -/
theorem exists_kernelPair (a : (schemeYoneda S).obj U ⟶ F) (ha : IsRepresentableMorphism a) :
    ∃ (R : Over S) (t s : R ⟶ U),
      IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a ∧
        IsEquivRel t.left s.left := by
  let t := Functor.relativelyRepresentable.fst' ha a
  let s := Functor.relativelyRepresentable.snd ha a
  have h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a :=
    Functor.relativelyRepresentable.isPullback' ha a
  exact ⟨_, t, s, h, isEquivRel_of_isPullback a t s h⟩

end KernelPair

section Restriction

variable {U R : Scheme.{u}} {t s : R ⟶ U}

/-- The symmetry of an equivalence relation, as an involution of `R`. -/
theorem IsEquivRel.exists_swap (h : IsEquivRel t s) :
    ∃ σ : R ⟶ R, σ ≫ t = s ∧ σ ≫ s = t ∧ σ ≫ σ = 𝟙 R := by
  obtain ⟨σ, hσt, hσs⟩ := h.symm R (𝟙 R)
  rw [Category.id_comp] at hσt hσs
  refine ⟨σ, hσt, hσs, ?_⟩
  have := h.mono
  rw [← cancel_mono (prod.lift t s)]
  apply prod.hom_ext
  · simp [hσt, hσs]
  · simp [hσt, hσs]

/-- The restriction of `t` to an invariant open `W`, with source `s⁻¹ W`. -/
def restrictT (t s : R ⟶ U) (W : U.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    (s ⁻¹ᵁ W).toScheme ⟶ W :=
  (R.isoOfEq hW).hom ≫ t ∣_ W

lemma restrictT_ι (t s : R ⟶ U) (W : U.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    restrictT t s W hW ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t := by
  rw [restrictT, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

lemma restrictS_ι (s : R ⟶ U) (W : U.Opens) : s ∣_ W ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s :=
  morphismRestrict_ι s W

/-- A morphism to `R` whose composite with `s` lands in `W` factors through `s⁻¹ W`. -/
lemma exists_lift_preimage {T : Scheme.{u}} (s : R ⟶ U) (W : U.Opens) (g : T ⟶ R)
    (hg : ∀ x, s (g x) ∈ W) : ∃ g' : T ⟶ (s ⁻¹ᵁ W).toScheme, g' ≫ (s ⁻¹ᵁ W).ι = g := by
  have hsub : Set.range g ⊆ Set.range (s ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hg x
  exact ⟨_root_.AlgebraicGeometry.IsOpenImmersion.lift _ g hsub,
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩

/-- An equivalence relation restricts to an invariant open. -/
theorem IsEquivRel.restrict (h : IsEquivRel t s) (W : U.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    IsEquivRel (restrictT t s W hW) (s ∣_ W) := by
  have ht := restrictT_ι t s W hW
  have hs := restrictS_ι s W
  have hmemt : ∀ y : (s ⁻¹ᵁ W).toScheme, t ((s ⁻¹ᵁ W).ι y) ∈ W := by
    intro y
    have : (s ⁻¹ᵁ W).ι y ∈ t ⁻¹ᵁ W := by
      rw [← hW]
      exact y.2
    exact this
  have hmems : ∀ y : (s ⁻¹ᵁ W).toScheme, s ((s ⁻¹ᵁ W).ι y) ∈ W := fun y ↦ y.2
  refine ⟨⟨fun {T} g k hgk => ?_⟩, fun T a₀ => ?_, fun T r => ?_, fun T r r' hrr => ?_⟩
  · have h₁ : g ≫ restrictT t s W hW = k ≫ restrictT t s W hW := by
      simpa using congrArg (· ≫ prod.fst) hgk
    have h₂ : g ≫ s ∣_ W = k ≫ s ∣_ W := by simpa using congrArg (· ≫ prod.snd) hgk
    have h₁' : (g ≫ (s ⁻¹ᵁ W).ι) ≫ t = (k ≫ (s ⁻¹ᵁ W).ι) ≫ t := by
      rw [Category.assoc, Category.assoc, ← ht, ← Category.assoc, h₁, Category.assoc]
    have h₂' : (g ≫ (s ⁻¹ᵁ W).ι) ≫ s = (k ≫ (s ⁻¹ᵁ W).ι) ≫ s := by
      rw [Category.assoc, Category.assoc, ← hs, ← Category.assoc, h₂, Category.assoc]
    have := h.mono
    have hgk' : g ≫ (s ⁻¹ᵁ W).ι = k ≫ (s ⁻¹ᵁ W).ι := by
      rw [← cancel_mono (prod.lift t s)]
      apply prod.hom_ext <;> simp [h₁', h₂']
    exact (cancel_mono _).mp hgk'
  · obtain ⟨r, hr₁, hr₂⟩ := h.refl T (a₀ ≫ W.ι)
    obtain ⟨r', hr'⟩ := exists_lift_preimage s W r (fun x ↦ by
      rw [← Scheme.Hom.comp_apply, hr₂, Scheme.Hom.comp_apply]
      exact (a₀ x).2)
    refine ⟨r', ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, ht, ← Category.assoc, hr', hr₁]
    · rw [← cancel_mono W.ι, Category.assoc, hs, ← Category.assoc, hr', hr₂]
  · obtain ⟨r₁, hr₁, hr₂⟩ := h.symm T (r ≫ (s ⁻¹ᵁ W).ι)
    obtain ⟨r', hr'⟩ := exists_lift_preimage s W r₁ (fun x ↦ by
      rw [← Scheme.Hom.comp_apply, hr₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hmemt _)
    refine ⟨r', ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, ht, ← Category.assoc, hr', hr₁, Category.assoc,
        Category.assoc, hs]
    · rw [← cancel_mono W.ι, Category.assoc, hs, ← Category.assoc, hr', hr₂, Category.assoc,
        Category.assoc, ht]
  · have hrr' : (r ≫ (s ⁻¹ᵁ W).ι) ≫ s = (r' ≫ (s ⁻¹ᵁ W).ι) ≫ t := by
      rw [Category.assoc, Category.assoc, ← hs, ← ht, ← Category.assoc, hrr, Category.assoc]
    obtain ⟨r₁, hr₁, hr₂⟩ := h.trans T _ _ hrr'
    obtain ⟨r'', hr''⟩ := exists_lift_preimage s W r₁ (fun x ↦ by
      rw [← Scheme.Hom.comp_apply, hr₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hmems _)
    refine ⟨r'', ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, ht, ← Category.assoc, hr'', hr₁, Category.assoc,
        Category.assoc, ht]
    · rw [← cancel_mono W.ι, Category.assoc, hs, ← Category.assoc, hr'', hr₂, Category.assoc,
        Category.assoc, hs]

/-- On an invariant open, the restricted `t` is the restricted `s` precomposed with an
automorphism of `s⁻¹ W`. -/
theorem IsEquivRel.exists_iso_restrictT (h : IsEquivRel t s) (W : U.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ φ : (s ⁻¹ᵁ W).toScheme ≅ (s ⁻¹ᵁ W).toScheme, φ.hom ≫ s ∣_ W = restrictT t s W hW := by
  obtain ⟨σ, hσt, hσs, hσσ⟩ := h.exists_swap
  have hmemt : ∀ y : (s ⁻¹ᵁ W).toScheme, t ((s ⁻¹ᵁ W).ι y) ∈ W := by
    intro y
    have : (s ⁻¹ᵁ W).ι y ∈ t ⁻¹ᵁ W := by
      rw [← hW]
      exact y.2
    exact this
  obtain ⟨φ, hφ⟩ := exists_lift_preimage s W ((s ⁻¹ᵁ W).ι ≫ σ) (fun x ↦ by
    rw [← Scheme.Hom.comp_apply, Category.assoc, hσs]
    exact hmemt x)
  have hφφ : φ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono (s ⁻¹ᵁ W).ι, Category.assoc, hφ, ← Category.assoc, hφ, Category.assoc,
      hσσ, Category.comp_id, Category.id_comp]
  refine ⟨⟨φ, φ, hφφ, hφφ⟩, ?_⟩
  change φ ≫ s ∣_ W = _
  rw [← cancel_mono W.ι, Category.assoc, restrictS_ι, ← Category.assoc, hφ, Category.assoc,
    hσs, restrictT_ι]

end Restriction

end Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation
