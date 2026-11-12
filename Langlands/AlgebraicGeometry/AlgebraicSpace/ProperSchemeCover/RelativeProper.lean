import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.Closedness
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Represented properness of the weak Chow cover

For weak Chow data `D`, every base change of the cover `φ : h_U → X` to a scheme `T` is a
proper morphism of schemes. Separatedness and finite type come from the closed immersion
`U ×_X T ⟶ U ×_S T`. Universal closedness descends along the étale surjective quasi-compact
morphism `W ×_X T ⟶ T`, over which the base change becomes a base change of the proper
projection `U ×_X W ⟶ W`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

theorem isPullback_congr_right {C : Type*} [Category C] {P A B Z : C} {a : P ⟶ A}
    {b : P ⟶ B} {c : A ⟶ Z} {d d' : B ⟶ Z} (h : IsPullback a b c d) (e : d = d') :
    IsPullback a b c d' := by
  subst e
  exact h

namespace ChowData

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ChowData X)

/-- The base change of the cover to a scheme `T` is separated and locally of finite type. -/
theorem isSeparated_snd {T : Over S} (g : (schemeYoneda S).obj T ⟶ X.presheaf) :
    _root_.AlgebraicGeometry.IsSeparated (spacePullbackSnd D.φ g).left ∧
      LocallyOfFiniteType (spacePullbackSnd D.φ g).left := by
  have := isClosedImmersion_spacePullbackLift D.φ g D.separated
  have h : spacePullbackSnd D.φ g =
      lift (spacePullbackFst D.φ g) (spacePullbackSnd D.φ g) ≫ snd D.U T :=
    (lift_snd _ _).symm
  rw [h, Over.comp_left, Over.snd_left]
  exact ⟨inferInstance, inferInstance⟩

/-- The base change of the chart to a scheme `T` is étale, surjective and quasi-compact. -/
theorem descent_snd {T : Over S} (g : (schemeYoneda S).obj T ⟶ X.presheaf) :
    ((@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (spacePullbackSnd D.π g).left := by
  have := etale_spacePullbackSnd D.π g D.etale
  have := isClosedImmersion_spacePullbackLift D.π g D.separated
  have hq : QuasiCompact (spacePullbackSnd D.π g).left := by
    have h : spacePullbackSnd D.π g =
        lift (spacePullbackFst D.π g) (spacePullbackSnd D.π g) ≫ snd D.W T :=
      (lift_snd _ _).symm
    rw [h, Over.comp_left, Over.snd_left]
    infer_instance
  exact ⟨⟨surjective_spacePullbackSnd D.π g D.surjective, inferInstance⟩, hq⟩

/-- The base change of the cover to a scheme `T` is universally closed. -/
theorem universallyClosed_snd {T : Over S} (g : (schemeYoneda S).obj T ⟶ X.presheaf) :
    UniversallyClosed (spacePullbackSnd D.φ g).left := by
  let y := schemeYoneda S
  -- `T' = W ×_X T`, with `f : T' ⟶ T` and `f' : T' ⟶ W`.
  let f := spacePullbackSnd D.π g
  let f' := spacePullbackFst D.π g
  -- `V = U ×_X T` and `V' = U ×_X T'`.
  let v := spacePullbackSnd D.φ g
  let v' := spacePullbackSnd D.φ (y.map f ≫ g)
  let u' := spacePullbackFst D.φ (y.map f ≫ g)
  have hV := spacePullback_isPullback D.φ g
  have h3 := spacePullback_isPullback D.φ (y.map f ≫ g)
  have h3' : IsPullback (y.map u') (y.map v') D.φ (y.map f' ≫ D.π) :=
    isPullback_congr_right h3 (spacePullback_w D.π g).symm
  -- The square `V' ⟶ V` over `T' ⟶ T` is a pullback.
  let w : spacePullback D.φ (y.map f ≫ g) ⟶ spacePullback D.φ g :=
    spacePullbackLift u' (v' ≫ f) (by rw [Functor.map_comp_assoc]; exact h3.w)
  have hA : IsPullback (y.map w) (y.map v') (y.map v) (y.map f) :=
    IsPullback.of_right (h₁₂ := y.map (spacePullbackFst D.φ g))
      (by rw [← Functor.map_comp, spacePullbackLift_fst]; exact h3)
      (by rw [← Functor.map_comp, ← Functor.map_comp, spacePullbackLift_snd]) hV
  have hA' := (hA.of_map_of_faithful).map (Over.forget S)
  -- The square `V' ⟶ U ×_X W` over `T' ⟶ W` is a pullback.
  let k : spacePullback D.φ (y.map f ≫ g) ⟶ D.Q :=
    spacePullbackLift u' (v' ≫ f') (by rw [Functor.map_comp_assoc]; exact h3'.w)
  have hB : IsPullback (y.map k) (y.map v') (y.map D.q₂) (y.map f') :=
    IsPullback.of_right (h₁₂ := y.map D.q₁)
      (by rw [← Functor.map_comp, spacePullbackLift_fst]; exact h3')
      (by rw [← Functor.map_comp, ← Functor.map_comp, spacePullbackLift_snd])
      (spacePullback_isPullback D.φ D.π)
  have hB' := (hB.of_map_of_faithful).map (Over.forget S)
  have huc : UniversallyClosed v'.left :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) hB'
      (inferInstanceAs (UniversallyClosed D.q₂.left))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})) hA'.flip
    (D.descent_snd g) huc

/-- **Represented properness.** Every base change of the cover `φ` to a scheme is proper. -/
theorem relative_isProper_φ :
    (MorphismProperty.inverseImage @_root_.AlgebraicGeometry.IsProper (Over.forget S)).relative
      (schemeYoneda S) D.φ := by
  have : (MorphismProperty.inverseImage @_root_.AlgebraicGeometry.IsProper
      (Over.forget S)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.relative_of_snd (X.representable_from_scheme D.φ) (fun T g => by
    obtain ⟨h₁, h₂⟩ := D.isSeparated_snd g
    have h₃ := D.universallyClosed_snd g
    exact { toIsSeparated := h₁, toUniversallyClosed := h₃, toLocallyOfFiniteType := h₂ })

end ChowData

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
