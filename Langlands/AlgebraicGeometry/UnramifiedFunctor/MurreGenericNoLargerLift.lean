import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusOpen
import Mathlib.RingTheory.Etale.Basic

/-! # Murre's Lemma 2, case (b): no larger lifts near a point over the generic point

A step of Murre's proof of Lemma 2 (Bourbaki exp. 294), case (b): for a closed subscheme
`Spec (R'/𝔍)` of an étale `Spec R`-scheme `Spec R'` and an element `ξ` of `F` over it that is
infinitesimally étale at a point `y` lying over the generic point of the irreducible scheme
`Spec R`, condition (F8) gives a neighbourhood of `y` at whose points `ξ` lifts to no closed
subscheme of `Spec 𝒪_{Spec R', w}` strictly larger than `Spec (𝒪_{Spec R', w}/𝔍)`. This module
states the proposition; it proves nothing. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

/-- Murre's Lemma 2, first half of case (b). Let `R` be a noetherian ring and `F` a presheaf on
`Over (Spec R)` satisfying the conditions of Murre's Theorem 1. Let `R'` be an étale
`R`-algebra, `𝔍` an ideal of `R'`, `ξ ∈ F(Spec (R'/𝔍))` (with `Spec (R'/𝔍)` over `Spec R`
through `Spec R'`), and `y` a point of `Spec (R'/𝔍)` at which `ξ` is infinitesimally étale and
whose image in `Spec R` lies in the nilradical (so `Spec R` is irreducible and `y` lies over its
generic point). Then there is an open neighbourhood `V` of `y` such that for every `w ∈ V`, with
`R'_w` the local ring of `Spec R'` at the image of `w`, the ideal `𝔍 R'_w` is nilpotent and the
restriction of `ξ` to `Spec (R'_w/𝔍 R'_w)` lifts to no `Spec (R'_w/J)` with `J < 𝔍 R'_w`. -/
def GenericNoLargerLiftStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (𝔍 : Ideal R')
      (ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍))))
      (y : PrimeSpectrum (R' ⧸ 𝔍)), InfinitesimallyEtaleAt F ξ y →
      y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) ≤ nilradical R →
      ∃ V : Set (PrimeSpectrum (R' ⧸ 𝔍)), IsOpen V ∧ y ∈ V ∧
        ∀ w ∈ V,
          IsNilpotent (𝔍.map (algebraMap R'
            (Localization.AtPrime (w.asIdeal.comap (Ideal.Quotient.mk 𝔍))))) ∧
          NoLargerLift (Localization.AtPrime (w.asIdeal.comap (Ideal.Quotient.mk 𝔍))) ξ

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
