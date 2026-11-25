/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality

/-!
# Stalks at the closed point of a strictly henselian local scheme

Let `R` be a strictly henselian local ring and `x : Spec Ω ⟶ Spec R` a geometric point lying
over the closed point. Every pointed étale neighbourhood `(V, v)` of `x` receives exactly one
morphism of pointed neighbourhoods from `(Spec R, x)`: this is a section of the étale morphism
`V ⟶ Spec R` through `v` (`AlgebraicGeometry.existsUnique_section_of_etale`). Hence
`(Spec R, x)` is an initial pointed étale neighbourhood, and the stalk at `x` of any presheaf on
the small étale site of `Spec R` is its value on `Spec R`.

## Main definitions

- `AlgebraicGeometry.Scheme.topFiberElement`: the pointed étale neighbourhood `(Spec R, x)`.

## Main statements

- `AlgebraicGeometry.Scheme.isInitialTopFiberElement`: it is initial.
- `AlgebraicGeometry.Scheme.isIso_toPresheafFiber_top`: the germ map out of the global
  sections is an isomorphism onto the stalk at `x`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {R : CommRingCat.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (e : R ⟶ CommRingCat.of Ω)

/-- The terminal étale `Spec R`-scheme `Spec R` together with the geometric point `Spec e`, as
an element of the fibre functor of the point `pointSmallEtale (Spec.map e)`. -/
noncomputable def topFiberElement : (pointSmallEtale (Spec.map e)).fiber.Elements :=
  { obj := Etale.mk (𝟙 (Spec R))
    val := Over.homMk (U := Over.mk (Spec.map e))
      (V := (Etale.forget _).obj (Etale.mk (𝟙 (Spec R)))) (Spec.map e) (Category.comp_id _) }

@[simp]
lemma topFiberElement_fst : (topFiberElement e).1 = Etale.mk (𝟙 (Spec R)) :=
  rfl

variable [IsStrictlyHenselianLocalRing R]

/-- If the kernel of `e : R ⟶ Ω` is the maximal ideal of the strictly henselian local ring `R`,
the pointed étale neighbourhood `(Spec R, Spec e)` is initial: every pointed étale neighbourhood
`(V, v)` of `Spec e` has a unique section through `v`. -/
noncomputable def isInitialTopFiberElement (he : RingHom.ker e.hom = maximalIdeal R) :
    IsInitial (topFiberElement e) := by
  refine @IsInitial.ofUniqueHom _ _ _ (fun Y ↦ ?_) (fun Y f ↦ ?_)
  · obtain @⟨V, v⟩ := Y
    have hv : v.left ≫ V.hom = Spec.map e := Over.w v
    have hσ := existsUnique_section_of_etale e he V.hom v.left hv
    refine ⟨MorphismProperty.Over.homMk hσ.choose (by simpa using hσ.choose_spec.1.1),
      Over.OverMorphism.ext ?_⟩
    exact hσ.choose_spec.1.2
  · obtain @⟨V, v⟩ := Y
    obtain ⟨f, hf⟩ := f
    have hv : v.left ≫ V.hom = Spec.map e := Over.w v
    have hσ := existsUnique_section_of_etale e he V.hom v.left hv
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    have h₁ : f.left ≫ V.hom = 𝟙 _ := MorphismProperty.Over.w f
    have h₂ : Spec.map e ≫ f.left = v.left := congrArg CommaMorphism.left hf
    exact (hσ.unique ⟨h₁, h₂⟩ hσ.choose_spec.1).trans rfl

/-- **Stalks at the closed point of a strictly henselian local scheme.** If the kernel of
`e : R ⟶ Ω` is the maximal ideal of the strictly henselian local ring `R`, the germ map
`P(Spec R) ⟶ P_x` at `x = Spec e` is an isomorphism, for every presheaf `P` on the small étale
site of `Spec R`. -/
lemma isIso_toPresheafFiber_top (he : RingHom.ker e.hom = maximalIdeal R) {A : Type v}
    [Category.{w} A] [HasColimitsOfSize.{u, u} A] (P : (Spec R).Etaleᵒᵖ ⥤ A) :
    IsIso ((pointSmallEtale (Spec.map e)).toPresheafFiber (topFiberElement e).1
      (topFiberElement e).2 P) :=
  isIso_ι_of_isTerminal (isInitialTopFiberElement e he).op _

end AlgebraicGeometry.Scheme
