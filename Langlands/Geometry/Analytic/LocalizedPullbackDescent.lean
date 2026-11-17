import Langlands.Geometry.Analytic.StrongRefiningSourceSeparation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Pullback universal properties from refined strong maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C P T : SaturatedAtlasPresentation.{u, v, w} K}

/-- Localization detects equality of complete strong maps, by the published
bounded-algebra separation theorem on refining original source charts. -/
theorem localizationFunctor_map_injective :
    Function.Injective (fun f : A ⟶ B => localizationFunctor.map f) := by
  intro f g h
  apply SourceCategory.strongFunctor_map_injective
  apply sourceHomEquiv.injective
  change sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map f)) =
    sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map g))
  simpa only [Equiv.apply_symm_apply] using h

/-- Two localized arrows out of one original object have complete strong
numerators on a common full quasi-isomorphism source. -/
theorem exists_commonStrongNumerators
    (a : localizationFunctor.obj T ⟶ localizationFunctor.obj A)
    (b : localizationFunctor.obj T ⟶ localizationFunctor.obj B) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ T), s.IsQuasiIso ∧
      ∃ (a' : S ⟶ A) (b' : S ⟶ B),
        localizationFunctor.map s ≫ a = localizationFunctor.map a' ∧
        localizationFunctor.map s ≫ b = localizationFunctor.map b' := by
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction a
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction b
  let i := quasiIsoOreInclusion φ.s ψ.s ψ.hs
  let j := quasiIsoOreLift φ.s ψ.s ψ.hs
  have hij : j ≫ ψ.s = i ≫ φ.s := quasiIsoOre_square φ.s ψ.s ψ.hs
  refine ⟨quasiIsoOreSource φ.s ψ.s ψ.hs, i ≫ φ.s,
    (quasiIsomorphisms (K := K)).comp_mem _ _
      (isQuasiIso_quasiIsoOreInclusion φ.s ψ.s ψ.hs) φ.hs,
    i ≫ φ.f, j ≫ ψ.f, ?_, ?_⟩
  · rw [Functor.map_comp, Category.assoc,
      localizationFunctor_map_s_comp_localizedRightFraction, Functor.map_comp]
  · rw [← hij, Functor.map_comp, Category.assoc,
      localizationFunctor_map_s_comp_localizedRightFraction, Functor.map_comp]

/-- Any commuting localized cone over strong maps is represented on a common
full quasi-isomorphism source by an exactly commuting strong cone. -/
theorem exists_commutingStrongNumerators (f : A ⟶ C) (g : B ⟶ C)
    (a : localizationFunctor.obj T ⟶ localizationFunctor.obj A)
    (b : localizationFunctor.obj T ⟶ localizationFunctor.obj B)
    (h : a ≫ localizationFunctor.map f = b ≫ localizationFunctor.map g) :
    ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ T), s.IsQuasiIso ∧
      ∃ (a' : S ⟶ A) (b' : S ⟶ B),
        localizationFunctor.map s ≫ a = localizationFunctor.map a' ∧
        localizationFunctor.map s ≫ b = localizationFunctor.map b' ∧
        a' ≫ f = b' ≫ g := by
  obtain ⟨S, s, hs, a', b', ha, hb⟩ := exists_commonStrongNumerators a b
  refine ⟨S, s, hs, a', b', ha, hb, ?_⟩
  apply localizationFunctor_map_injective
  change localizationFunctor.map (a' ≫ f) = localizationFunctor.map (b' ≫ g)
  rw [Functor.map_comp, Functor.map_comp, ← ha, ← hb, Category.assoc, Category.assoc, h]

/-- Strong pullback data: the square commutes; every exactly commuting strong
cone lifts after a full quasi-isomorphism source refinement; and its two
projections jointly detect equality of complete strong maps. -/
def IsRefinedStrongPullback (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C) : Prop :=
  p ≫ f = q ≫ g ∧
    (∀ (T : SaturatedAtlasPresentation.{u, v, w} K) (a : T ⟶ A) (b : T ⟶ B),
      a ≫ f = b ≫ g →
        ∃ (S : SaturatedAtlasPresentation.{u, v, w} K) (s : S ⟶ T), s.IsQuasiIso ∧
          ∃ l : S ⟶ P, l ≫ p = s ≫ a ∧ l ≫ q = s ≫ b) ∧
    ∀ (T : SaturatedAtlasPresentation.{u, v, w} K) (a b : T ⟶ P),
      a ≫ p = b ≫ p → a ≫ q = b ≫ q → a = b

/-- Refined strong existence supplies every localized cone's lift. -/
theorem IsRefinedStrongPullback.exists_lift
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsRefinedStrongPullback p q f g)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a : Z ⟶ localizationFunctor.obj A) (b : Z ⟶ localizationFunctor.obj B)
    (hab : a ≫ localizationFunctor.map f = b ≫ localizationFunctor.map g) :
    ∃ l : Z ⟶ localizationFunctor.obj P,
      l ≫ localizationFunctor.map p = a ∧ l ≫ localizationFunctor.map q = b := by
  obtain ⟨T, hT⟩ := localizedObjectEquiv.surjective Z
  change localizationFunctor.obj T = Z at hT
  subst Z
  obtain ⟨S, s, hs, a', b', ha, hb, hab'⟩ :=
    exists_commutingStrongNumerators f g a b hab
  obtain ⟨R, r, hr, l, hlp, hlq⟩ := h.2.1 S a' b' hab'
  let φ : (quasiIsomorphisms (K := K)).RightFraction T P :=
    ⟨r ≫ s, (quasiIsomorphisms (K := K)).comp_mem _ _ hr hs, l⟩
  have : IsIso (localizationFunctor.map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
  refine ⟨localizedRightFraction φ, ?_, ?_⟩
  · apply (cancel_epi (localizationFunctor.map φ.s)).1
    rw [← Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
      ← Functor.map_comp, hlp]
    change localizationFunctor.map (r ≫ a') = localizationFunctor.map (r ≫ s) ≫ a
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, ha]
  · apply (cancel_epi (localizationFunctor.map φ.s)).1
    rw [← Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
      ← Functor.map_comp, hlq]
    change localizationFunctor.map (r ≫ b') = localizationFunctor.map (r ≫ s) ≫ b
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hb]

/-- Complete strong joint uniqueness implies joint uniqueness for all localized
arrows, after placing two numerators on one quasi-isomorphism source. -/
theorem IsRefinedStrongPullback.hom_ext
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsRefinedStrongPullback p q f g)
    {Z : LocalizedCategory.{u, v, w} (K := K)}
    (a b : Z ⟶ localizationFunctor.obj P)
    (hp : a ≫ localizationFunctor.map p = b ≫ localizationFunctor.map p)
    (hq : a ≫ localizationFunctor.map q = b ≫ localizationFunctor.map q) : a = b := by
  obtain ⟨T, hT⟩ := localizedObjectEquiv.surjective Z
  change localizationFunctor.obj T = Z at hT
  subst Z
  obtain ⟨S, s, hs, a', b', ha, hb⟩ := exists_commonStrongNumerators a b
  have hp' : a' ≫ p = b' ≫ p := by
    apply localizationFunctor_map_injective
    change localizationFunctor.map (a' ≫ p) = localizationFunctor.map (b' ≫ p)
    rw [Functor.map_comp, Functor.map_comp, ← ha, ← hb, Category.assoc, Category.assoc, hp]
  have hq' : a' ≫ q = b' ≫ q := by
    apply localizationFunctor_map_injective
    change localizationFunctor.map (a' ≫ q) = localizationFunctor.map (b' ≫ q)
    rw [Functor.map_comp, Functor.map_comp, ← ha, ← hb, Category.assoc, Category.assoc, hq]
  have heq := h.2.2 S a' b' hp' hq'
  have : IsIso (localizationFunctor.map s) := (localizedQuasiIso s hs).isIso_hom
  apply (cancel_epi (localizationFunctor.map s)).1
  rw [ha, hb, heq]

/-- Build the full categorical limit from refined strong existence and joint
bounded-map uniqueness. Every test object and arrow is localized. -/
def IsRefinedStrongPullback.isLimit
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsRefinedStrongPullback p q f g) :
    IsLimit (PullbackCone.mk (localizationFunctor.map p) (localizationFunctor.map q)
      (by rw [← Functor.map_comp, ← Functor.map_comp, h.1])) := by
  let w : localizationFunctor.map p ≫ localizationFunctor.map f =
      localizationFunctor.map q ≫ localizationFunctor.map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, h.1]
  let lift (s : PullbackCone (localizationFunctor.map f) (localizationFunctor.map g)) :=
    (h.exists_lift s.fst s.snd s.condition).choose
  have fac (s : PullbackCone (localizationFunctor.map f) (localizationFunctor.map g)) :=
    (h.exists_lift s.fst s.snd s.condition).choose_spec
  exact PullbackCone.IsLimit.mk w lift
    (fun s => (fac s).1) (fun s => (fac s).2)
    (fun s m hm₁ hm₂ => h.hom_ext m (lift s)
      (hm₁.trans (fac s).1.symm) (hm₂.trans (fac s).2.symm))

/-- Refined strong pullback data imply the actual localized pullback universal
property, with all three universes unchanged. -/
theorem IsRefinedStrongPullback.isPullback
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsRefinedStrongPullback p q f g) :
    IsPullback (localizationFunctor.map p) (localizationFunctor.map q)
      (localizationFunctor.map f) (localizationFunctor.map g) where
  w := by rw [← Functor.map_comp, ← Functor.map_comp, h.1]
  isLimit' := ⟨h.isLimit⟩

end Langlands.Analytic.SaturatedAtlasPresentation
