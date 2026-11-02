import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # Atlas geometry over a monomorphism to a scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A monomorphism into a scheme identifies the represented atlas kernel pair
with the scheme-theoretic kernel pair of the composite. -/
theorem atlasKernelPair_isPullback_of_mono
    {F : Presheaf S} {W Y R : Over S}
    (a : (schemeYoneda S).obj W ⟶ F)
    (f : F ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    (p₁ p₂ : R ⟶ W) (hp : IsPullback p₁ p₂ w w) :
    IsPullback ((schemeYoneda S).map p₁) ((schemeYoneda S).map p₂) a a := by
  have hcomp : IsPullback ((schemeYoneda S).map p₁) ((schemeYoneda S).map p₂)
      (a ≫ f) (a ≫ f) := by
    simpa only [hw] using hp.map (schemeYoneda S)
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors (a ≫ f) (a ≫ f) f a a rfl rfl _ hcomp.isLimit)

/-- The actual scheme kernel pair of an atlas composite, equipped with its
structure morphism to the base. -/
def atlasCompositeKernelPair {W Y : Over S} (w : W ⟶ Y) : Over S :=
  Over.mk (Limits.pullback.fst w.left w.left ≫ W.hom)

/-- The second projection of the scheme kernel pair of an etale chart over a
monomorphism is etale. -/
theorem etale_kernelPair_snd_of_mono
    {F : Presheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F) (ha : IsEtale a)
    (f : F ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w) :
    Etale (Limits.pullback.snd w.left w.left) := by
  let P : Over S := atlasCompositeKernelPair w
  let p₁ : P ⟶ W := Over.homMk (Limits.pullback.fst w.left w.left)
  let p₂ : P ⟶ W := Over.homMk (Limits.pullback.snd w.left w.left) (by
    dsimp [P, atlasCompositeKernelPair]
    rw [← Over.w w, ← Category.assoc, ← Limits.pullback.condition, Category.assoc])
  have hp : IsPullback p₁ p₂ w w := by
    apply IsPullback.of_map_of_faithful (Over.forget S)
    exact IsPullback.of_hasPullback w.left w.left
  exact ha.projection a ((schemeYoneda S).map p₁) p₂
    (atlasKernelPair_isPullback_of_mono a f w hw p₁ p₂ hp)

/-- The scheme composite of an etale chart with a monomorphism to a scheme is
formally unramified. -/
theorem formallyUnramified_of_etale_mono_composite
    {F : Presheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F) (ha : IsEtale a)
    (f : F ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w) :
    FormallyUnramified w.left := by
  have : Etale (Limits.pullback.snd w.left w.left) :=
    etale_kernelPair_snd_of_mono a ha f w hw
  let : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ g _ => inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal g)))
  have hsec : IsOpenImmersion
      (Limits.pullback.diagonal w.left ≫ Limits.pullback.snd w.left w.left) := by
    rw [Limits.pullback.diagonal_snd]
    infer_instance
  have : IsOpenImmersion (Limits.pullback.diagonal w.left) :=
    MorphismProperty.of_postcomp @IsOpenImmersion
      (Limits.pullback.diagonal w.left) (Limits.pullback.snd w.left w.left)
      ‹Etale _› hsec
  infer_instance

/-- If the same composite is locally of finite type, it is locally quasi-finite. -/
theorem locallyQuasiFinite_of_etale_mono_composite
    {F : Presheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F) (ha : IsEtale a)
    (f : F ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left] : LocallyQuasiFinite w.left := by
  have : FormallyUnramified w.left :=
    formallyUnramified_of_etale_mono_composite a ha f w hw
  exact GenericFiniteness.locallyQuasiFinite_of_formallyUnramified w.left

end Langlands.AlgebraicGeometry.AlgebraicSpace
