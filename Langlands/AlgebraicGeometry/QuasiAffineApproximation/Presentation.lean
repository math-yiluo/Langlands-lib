import Langlands.AlgebraicGeometry.QuasiAffineApproximation.Skeleton
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # A presentation of a finite surjective quasi-affine cover

Let `f : U ⟶ Y` be a finite surjective map from a scheme `U` over `S` to a quasi-compact
algebraic space `Y`. An affine étale atlas `a₀ : U₀ ⟶ Y` gives the étale equivalence relation
`E` of `a₀` on the affine scheme `U₀`. The fibre product `U₀ ×_Y U` carries the étale
equivalence relation `E'` of its étale surjective projection `q` to `U`; the other projection
`φ : U₀ ×_Y U ⟶ U₀` is finite surjective and cartesian from `E'` to `E`. Two points of `U` with
the same image in `Y` lift along `q` to two points with the same image under `φ`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open AlgebraicSpace EtaleEquivalenceRelation

variable {S : Scheme.{u}}

/-- The map of represented presheaves along a surjective morphism is surjective. -/
theorem isSurjective_map {U V : Over S} (j : U ⟶ V) (hj : Surjective j.left) :
    AlgebraicSpace.IsSurjective ((schemeYoneda S).map j) := by
  have : (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderBaseChange :=
    isStableUnderBaseChange_inverseImage_forget
  exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)) hj

set_option backward.isDefEq.respectTransparency.types false in
/-- Surjective maps of presheaves are stable under composition. -/
theorem isSurjective_comp {F G H : AlgebraicSpace.Presheaf S} {f : F ⟶ G} {g : G ⟶ H}
    (hf : AlgebraicSpace.IsSurjective f) (hg : AlgebraicSpace.IsSurjective g) :
    AlgebraicSpace.IsSurjective (f ≫ g) :=
  MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)).relative (schemeYoneda S)) f g hf hg

/-- A quasi-compact algebraic space has an étale surjective atlas from an affine scheme. -/
theorem exists_affine_atlas_of_isQuasiCompact {Y : AlgebraicSpace S} (hY : IsQuasiCompact Y) :
    ∃ (U₀ : Over S) (a₀ : (schemeYoneda S).obj U₀ ⟶ Y.presheaf),
      IsAffine U₀.left ∧ IsEtale a₀ ∧ AlgebraicSpace.IsSurjective a₀ := by
  obtain ⟨W, a, ha, has, hW⟩ := hY
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have : MorphismProperty.ContainsIdentities @Etale.{u} :=
    ⟨fun T => inferInstanceAs (Etale (𝟙 T))⟩
  obtain ⟨V, j, hjs, hje, hV⟩ :=
    Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource (@Etale.{u}) W.left
  let U₀ : Over S := Over.mk (j ≫ W.hom)
  let j' : U₀ ⟶ W := Over.homMk j
  exact ⟨U₀, (schemeYoneda S).map j' ≫ a, hV, (isEtale_map j' hje).comp ha,
    isSurjective_comp (isSurjective_map j' hjs) has⟩

/-- Part I: a finite surjective map from a scheme `U` over `Spec R` to a quasi-compact algebraic
space has the presentation required by `PresentationInterface`. -/
theorem presentationInterface : PresentationInterface.{u} := by
  intro R _ U Y f hqc _ _ hfin hsurj
  obtain ⟨U₀, a₀, hU₀, he, hes⟩ := exists_affine_atlas_of_isQuasiCompact hqc
  obtain ⟨Rel, t, s, h, ht, hs⟩ := exists_kernelPair he
  let c : (schemeYoneda _).obj U ⟶ Y.presheaf := hom f
  let hr := he.representable
  have hU := hr.isPullback c
  obtain ⟨φ, hφ⟩ := (schemeYoneda _).map_surjective (hr.fst c)
  rw [← hφ] at hU
  let q := hr.snd c
  have hqe : Etale q.left := he.projection c _ _ hU
  have hqs : Surjective q.left := hes.projection c _ _ hU
  have hφf : _root_.AlgebraicGeometry.IsFinite φ.left := hfin.projection a₀ _ _ hU.flip
  have hφs : Surjective φ.left := hsurj.projection a₀ _ _ hU.flip
  have hR := IsPullback.of_hasPullback q q
  have hRS : IsPullback (pullback.fst q q).left (pullback.snd q q).left q.left q.left :=
    hR.map (Over.forget _)
  have ht' : Etale (pullback.fst q q).left :=
    MorphismProperty.of_isPullback (P := @Etale) hRS.flip hqe
  have hs' : Etale (pullback.snd q q).left :=
    MorphismProperty.of_isPullback (P := @Etale) hRS hqe
  obtain ⟨g, hg₁, hg₂⟩ := exists_lift_of_isPullback h (pullback.fst q q ≫ φ)
    (pullback.snd q q ≫ φ) (by
      simp only [Functor.map_comp, Category.assoc, hU.w]
      simp only [← Functor.map_comp_assoc]
      rw [show pullback.fst q q ≫ q = pullback.snd q q ≫ q from pullback.condition])
  have : Etale q.left := hqe
  have hfl : Flat q.left := inferInstance
  have hlfp : LocallyOfFinitePresentation q.left := inferInstance
  refine ⟨ofKernelPair t s a₀ h ht hs, ofKernelPair _ _ _ (hR.map (schemeYoneda _)) ht' hs',
    φ.left, g.left, q.left, hU₀, ⟨?_, ?_⟩, hφf, hφs, hRS, hfl, hlfp, hqs, ?_⟩
  · change g.left ≫ t.left = (pullback.fst q q).left ≫ φ.left
    rw [← Over.comp_left, hg₁, Over.comp_left]
  · have big := (hR.map (schemeYoneda _)).paste_horiz hU
    rw [← Functor.map_comp, ← hg₁, Functor.map_comp, ← hU.w] at big
    have hsq : IsPullback g (pullback.snd q q) s φ :=
      isPullback_of_map (big.of_right (by rw [← Functor.map_comp, ← Functor.map_comp, hg₂]) h)
    exact hsq.map (Over.forget _)
  · rintro _ _ ⟨T, g₁, g₂, t₀, hcomm, rfl, rfl⟩
    let X := (schemeYoneda _).map g₁ ≫ c
    have hT := hr.isPullback X
    obtain ⟨ψ, hψ⟩ := (schemeYoneda _).map_surjective (hr.fst X)
    rw [← hψ] at hT
    have hTs : Surjective (hr.snd X).left := hes.projection X _ _ hT
    obtain ⟨t₁, ht₁⟩ := Surjective.surj (f := (hr.snd X).left) t₀
    have w₁ : (schemeYoneda _).map ψ ≫ a₀ =
        (schemeYoneda _).map (hr.snd X ≫ g₁) ≫ c := by
      rw [hT.w, Functor.map_comp, Category.assoc]
    have w₂ : (schemeYoneda _).map ψ ≫ a₀ =
        (schemeYoneda _).map (hr.snd X ≫ g₂) ≫ c := by
      rw [hT.w, Functor.map_comp, Category.assoc]
      exact congrArg ((schemeYoneda _).map (hr.snd X) ≫ ·) hcomm
    obtain ⟨ω₁, hω₁⟩ := (schemeYoneda _).map_surjective (hU.lift _ _ w₁)
    obtain ⟨ω₂, hω₂⟩ := (schemeYoneda _).map_surjective (hU.lift _ _ w₂)
    have hω₁φ : ω₁ ≫ φ = ψ :=
      (schemeYoneda _).map_injective (by rw [Functor.map_comp, hω₁, hU.lift_fst])
    have hω₂φ : ω₂ ≫ φ = ψ :=
      (schemeYoneda _).map_injective (by rw [Functor.map_comp, hω₂, hU.lift_fst])
    have hω₁q : ω₁ ≫ q = hr.snd X ≫ g₁ :=
      (schemeYoneda _).map_injective (by rw [Functor.map_comp, hω₁, hU.lift_snd])
    have hω₂q : ω₂ ≫ q = hr.snd X ≫ g₂ :=
      (schemeYoneda _).map_injective (by rw [Functor.map_comp, hω₂, hU.lift_snd])
    refine ⟨ω₁.left t₁, ω₂.left t₁, ?_, ?_, ?_⟩
    · change q.left (ω₁.left t₁) = g₁.left t₀
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hω₁q, Over.comp_left, Scheme.Hom.comp_apply,
        ht₁]
    · change q.left (ω₂.left t₁) = g₂.left t₀
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hω₂q, Over.comp_left, Scheme.Hom.comp_apply,
        ht₁]
    · change φ.left (ω₁.left t₁) = φ.left (ω₂.left t₁)
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hω₁φ, ← Scheme.Hom.comp_apply,
        ← Over.comp_left, hω₂φ]

end Langlands.AlgebraicGeometry.QuasiAffineApproximation
