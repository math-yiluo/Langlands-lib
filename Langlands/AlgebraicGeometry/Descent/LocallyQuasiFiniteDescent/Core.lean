import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.EqLocusPushout
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Transport
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Descent of a quasi-affine fppf base change over an affine scheme -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace

/-- A commutative square stays a pullback square after cancelling a monomorphism from the
common target. -/
theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y Z Z' : C}
    {k₁ : P ⟶ X} {k₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (ι : Z ⟶ Z') [Mono ι]
    (H : IsPullback k₁ k₂ (f ≫ ι) (g ≫ ι)) : IsPullback k₁ k₂ f g := by
  refine ⟨⟨(cancel_mono ι).mp (by simpa only [Category.assoc] using H.w)⟩, ⟨?_⟩⟩
  refine PullbackCone.IsLimit.mk _
    (fun s => H.lift s.fst s.snd (by rw [reassoc_of% s.condition])) ?_ ?_ ?_
  · intro s
    exact H.lift_fst _ _ _
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h₁ h₂
    exact H.hom_ext (by rw [h₁, H.lift_fst]) (by rw [h₂, H.lift_snd])

variable {S : Scheme.{u}}

/-- The underlying square of schemes of a pullback in `Over S`, with the two maps to `T`
factored through a monomorphism `D ⟶ T`. -/
theorem isPullback_left_of_factor {X V T : Over S} (f : X ⟶ T) (g : V ⟶ T) {D : Scheme.{u}}
    (ι : D ⟶ T.left) [Mono ι] (f' : X.left ⟶ D) (g' : V.left ⟶ D) (hf : f' ≫ ι = f.left)
    (hg : g' ≫ ι = g.left) :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f' g' := by
  apply isPullback_of_comp_mono ι
  rw [hf, hg]
  exact (IsPullback.of_hasPullback f g).map (Over.forget S)

/-- The map on sections over the whole schemes is the map on global sections. -/
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app f (U := ⊤)

/-- Flat base change of global sections: for a pullback square over an affine scheme whose
right map is flat with affine source, and whose left corner is quasi-compact and
quasi-separated, global sections form a pushout square of rings. -/
theorem isPushout_appTop_of_isPullback {P X Y Z : Scheme.{u}} {k₁ : P ⟶ X} {k₂ : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback k₁ k₂ f g) [IsAffine Z] [IsAffine Y] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPushout f.appTop g.appTop k₁.appTop k₂.appTop := by
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top le_top (by simp) (isAffineOpen_top Z)
    (isAffineOpen_top Y) isCompact_univ isQuasiSeparated_univ
  convert (isIso_pushoutSection_iff H _ _ _).mp this using 1 <;>
    exact (appLE_top_top _ _).symm

/-- Global sections of a composite in `Over S`. -/
theorem appTop_comp_eq {X Y Y' Z : Over S} {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z} {f₂ : X ⟶ Y'}
    {g₂ : Y' ⟶ Z} (h : f₁ ≫ g₁ = f₂ ≫ g₂) :
    g₁.left.appTop ≫ f₁.left.appTop = g₂.left.appTop ≫ f₂.left.appTop :=
  congrArg (fun φ => φ.left.appTop) h

/-- Core descent step. Let `F` be an fppf sheaf over `S` with a map `p` to `T`, and let
`W ⟶ V` represent the base change of `p` along `g : V ⟶ T`, with `c : W ⟶ F` locally
surjective. Suppose `g` factors through a monomorphism `ι : D ⟶ T` from an affine scheme
`D`, by a flat morphism `g' : V ⟶ D` of finite presentation with `V` affine, and that `W` is
quasi-affine. Then `F` is represented by a scheme, through which `c` factors. -/
theorem exists_iso_of_quasiAffine {F : FppfSheaf S} {T V W : Over S}
    {p : F.obj ⟶ (schemeYoneda S).obj T} {g : V ⟶ T} {w : W ⟶ V}
    {c : (schemeYoneda S).obj W ⟶ F.obj}
    (hpb : IsPullback c ((schemeYoneda S).map w) p ((schemeYoneda S).map g))
    (hc : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) c)
    {D : Scheme.{u}} [IsAffine D] (ι : D ⟶ T.left) [Mono ι] (g' : V.left ⟶ D)
    (hg : g' ≫ ι = g.left) [IsAffine V.left] [Flat g'] [LocallyOfFinitePresentation g']
    [W.left.IsQuasiAffine] :
    ∃ (Y : Over S) (q : W ⟶ Y) (e : (schemeYoneda S).obj Y ≅ F.obj),
      (schemeYoneda S).map q ≫ e.hom = c := by
  classical
  -- The two pullback squares, as squares of schemes over `D`.
  have hK : IsPullback (pullback.fst (w ≫ g) g).left (pullback.snd (w ≫ g) g).left
      (w.left ≫ g') g' :=
    isPullback_left_of_factor _ _ ι _ _ (by rw [Category.assoc, hg, Over.comp_left]) hg
  have hP : IsPullback (pullback.fst (pullback.snd (w ≫ g) g ≫ g) g).left
      (pullback.snd (pullback.snd (w ≫ g) g ≫ g) g).left
      ((pullback.snd (w ≫ g) g).left ≫ g') g' :=
    isPullback_left_of_factor _ _ ι _ _ (by rw [Category.assoc, hg, Over.comp_left]) hg
  -- `W ×_T V` is quasi-affine, being affine over `W`.
  have : IsAffineHom (pullback.fst (w ≫ g) g).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hK.flip inferInstance
  have : (pullback (w ≫ g) g).left.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (pullback.fst (w ≫ g) g).left
  -- Flat base change of global sections.
  have h₁ := isPushout_appTop_of_isPullback hK
  have hE := isPushout_appTop_of_isPullback hP
  -- The diagonal is a section of the second map, so the latter is injective on sections.
  have hsec : (secondMap hpb).left.appTop ≫
      (pullback.lift (𝟙 W) w (by simp) : W ⟶ pullback (w ≫ g) g).left.appTop = 𝟙 _ := by
    have := congrArg (fun φ => φ.left.appTop) (diag_secondMap hpb)
    simpa using this
  have hinj : Function.Injective (secondMap hpb).left.appTop.hom :=
    Function.LeftInverse.injective
      (g := (pullback.lift (𝟙 W) w (by simp) : W ⟶ pullback (w ≫ g) g).left.appTop.hom)
      (fun x => by simpa using congrArg (fun φ => φ.hom x) hsec)
  obtain ⟨B, rB, ιB, hB, hιB⟩ := exists_isPushout_eqLocus g'.appTop g'.flat_appTop
    w.left.appTop (pullback.fst (w ≫ g) g).left.appTop (secondMap hpb).left.appTop
    (pullback.snd (w ≫ g) g).left.appTop h₁
    (pullback.fst (pullback.snd (w ≫ g) g ≫ g) g).left.appTop
    (pullback.snd (pullback.snd (w ≫ g) g ≫ g) g).left.appTop hE
    (firstLift w g).left.appTop (secondLift hpb).left.appTop
    (appTop_comp_eq firstLift_fst) (appTop_comp_eq (secondLift_fst hpb))
    (congrArg (fun φ => φ.left.appTop) (firstLift_snd (w := w) (g := g)))
    (congrArg (fun φ => φ.left.appTop) (secondLift_snd hpb))
    (congrArg (fun φ => φ.left.appTop) (secondMap_w hpb))
    (appTop_comp_eq (firstLift_secondMap hpb)) hinj
  -- The spectrum of the pushout square.
  have hSpec := isPullback_SpecMap_of_isPushout rB g'.appTop ιB w.left.appTop hB
  have hSr : Spec.map g'.appTop = V.left.isoSpec.inv ≫ g' ≫ D.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : Flat (Spec.map g'.appTop) := by rw [hSr]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map g'.appTop) := by rw [hSr]; infer_instance
  have : Flat (Spec.map ιB) :=
    MorphismProperty.of_isPullback (P := @Flat) hSpec.flip inferInstance
  have : LocallyOfFinitePresentation (Spec.map ιB) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hSpec.flip
      inferInstance
  -- The open image `U` of `W` in `Spec B`.
  let ω : W.left ⟶ Spec B := W.left.toSpecΓ ≫ Spec.map ιB
  have : Flat ω := inferInstance
  have : LocallyOfFinitePresentation ω := inferInstance
  let U : (Spec B).Opens := ⟨Set.range ω, ω.isOpenMap.isOpen_range⟩
  have hωU : Set.range ω ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_rfl
  let q' : W.left ⟶ U := IsOpenImmersion.lift U.ι ω hωU
  have hq'fac : q' ≫ U.ι = ω := IsOpenImmersion.lift_fac _ _ _
  have : MorphismProperty.HasOfPostcompProperty @Flat
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  have : MorphismProperty.HasOfPostcompProperty @LocallyOfFinitePresentation
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  have : Flat q' :=
    MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms _) (W := @Flat) q' U.ι
      (inferInstanceAs (Mono U.ι)) (by rw [hq'fac]; infer_instance)
  have : LocallyOfFinitePresentation q' :=
    MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms _)
      (W := @LocallyOfFinitePresentation) q' U.ι (inferInstanceAs (Mono U.ι))
      (by rw [hq'fac]; infer_instance)
  have : Surjective q' := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    change (q' ≫ U.ι) x = y.val
    rw [hq'fac]
    exact hx
  -- The descended scheme over `T`.
  have hkey : ω ≫ Spec.map rB ≫ D.isoSpec.inv = w.left ≫ g' := by
    have h1 : ω ≫ Spec.map rB = (w.left ≫ g') ≫ D.isoSpec.hom := by
      simp only [ω, Category.assoc, ← Spec.map_comp, hB.w]
      rw [← Scheme.Hom.comp_appTop, ← Scheme.toSpecΓ_naturality]
      rfl
    rw [reassoc_of% h1, Iso.hom_inv_id, Category.comp_id]
  let φ : (U : Scheme.{u}) ⟶ T.left := U.ι ≫ Spec.map rB ≫ D.isoSpec.inv ≫ ι
  have hqφ : q' ≫ φ = w.left ≫ g.left := by
    simp only [φ, ← hg]
    rw [reassoc_of% hq'fac, reassoc_of% hkey]
  let Y : Over S := Over.mk (φ ≫ T.hom)
  let y : Y ⟶ T := Over.homMk φ rfl
  let q : W ⟶ Y := Over.homMk q' (by
    change q' ≫ φ ≫ T.hom = W.hom
    rw [reassoc_of% hqφ, Over.w g, Over.w w])
  have hy : q ≫ y = w ≫ g := Over.OverMorphism.ext hqφ
  -- `q` identifies the two maps `W ×_T V ⟶ W`.
  have hqq : pullback.fst (w ≫ g) g ≫ q = secondMap hpb ≫ q := by
    apply Over.OverMorphism.ext
    change (pullback.fst (w ≫ g) g).left ≫ q' = (secondMap hpb).left ≫ q'
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hq'fac]
    simp only [ω, ← Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Category.assoc, ← Spec.map_comp, hιB]
  -- `q` and `w` are jointly monic.
  have hmono : ∀ {Z : Over S} (a b : Z ⟶ W), a ≫ q = b ≫ q → a ≫ w = b ≫ w → a = b := by
    intro Z a b h₁ h₂
    have h₁' : a.left ≫ q' = b.left ≫ q' := congrArg (fun φ => φ.left) h₁
    have h₂' : a.left ≫ w.left = b.left ≫ w.left := congrArg (fun φ => φ.left) h₂
    apply Over.OverMorphism.ext
    rw [← cancel_mono W.left.toSpecΓ]
    apply hSpec.hom_ext
    · rw [Category.assoc, Category.assoc]
      change a.left ≫ ω = b.left ≫ ω
      rw [← hq'fac, reassoc_of% h₁']
    · rw [Category.assoc, Category.assoc, ← Scheme.toSpecΓ_naturality, reassoc_of% h₂']
  have hker := app_eq_app_iff_comp_eq hpb q y hy hqq hmono
  have : Flat q.left := inferInstanceAs (Flat q')
  have : LocallyOfFinitePresentation q.left := inferInstanceAs (LocallyOfFinitePresentation q')
  have : Surjective q.left := inferInstanceAs (Surjective q')
  obtain ⟨e, he⟩ := exists_iso_of_locallySurjective_of_same_kernel c q hc
    (isLocallySurjective_schemeYoneda_map q) hker
  exact ⟨Y, q, e, he⟩

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
