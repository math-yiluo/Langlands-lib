import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusOpen
import Mathlib.RingTheory.Etale.Basic

/-! # Murre's Lemma 2 for closed subschemes of étale schemes

The case of Murre's Lemma 2 (`MurreEtaleLocusOpenStatement`) in which the chart is a closed
subscheme `Spec (R'/𝔍)` of the spectrum of an étale `R`-algebra `R'`, and the statement that
this case implies the general one. Murre (Bourbaki exp. 294, proof of Lemma 2) begins with this
reduction: an unramified morphism of finite type is, locally on the source, a closed immersion
into an étale scheme (EGA IV 18.4.7). This module states both propositions; it proves
nothing. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

/-- Murre's Lemma 2 for a closed subscheme `Spec (R'/𝔍)` of an étale `R`-scheme `Spec R'`.
Let `R` be a noetherian ring and `F` a presheaf on `Over (Spec R)` satisfying the conditions,
whose base change to `Spec 𝒪_{Spec R, s}` is representable (by a separated, locally of finite
type, formally unramified scheme) for every point `s`, and whose base change to every closed
subscheme `Spec (R/I)` with `I ≠ 0` is representable in the same way. Let `R'` be an étale
`R`-algebra, `𝔍` an ideal of `R'`, and `ξ ∈ F(Spec (R'/𝔍))`, where `Spec (R'/𝔍)` lies over
`Spec R` through `Spec R'`. Then the set of points of `Spec (R'/𝔍)` at which `ξ` is
infinitesimally étale is open. -/
def ClosedEtaleLocusOpenStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    (∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F)) →
    (∀ I : Ideal R, I ≠ ⊥ →
      UnramifiedRepresentable (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F)) →
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (𝔍 : Ideal R')
      (ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍)))),
      IsOpen {y | InfinitesimallyEtaleAt F ξ y}

/-- The reduction step of Murre's proof of Lemma 2: the case of closed subschemes of étale
schemes (`ClosedEtaleLocusOpenStatement`) implies Lemma 2 (`MurreEtaleLocusOpenStatement`). -/
def ClosedReductionStatement : Prop :=
  ClosedEtaleLocusOpenStatement.{u, v} → MurreEtaleLocusOpenStatement.{u, v}

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
