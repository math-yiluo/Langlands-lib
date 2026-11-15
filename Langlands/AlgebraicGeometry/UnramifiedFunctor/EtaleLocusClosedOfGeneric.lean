import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosed

/-! # Murre's Lemma 2 for closed subschemes of étale charts, from the generic case

Murre's proof of Lemma 2 (Bourbaki exp. 294) treats a point `y` of the étale locus in two
cases, according to whether the prime of the base below `y` is a generic point (case (b)) or
not (case (a)). This module states that the closed-subscheme form of Lemma 2
(`ClosedEtaleLocusOpenStatement`) follows from the first half of case (b): near a point `y`
of the étale locus lying over the nilradical of `R`, the ideal `𝔍` is nilpotent in the local
rings `O_w = R'_{P_w}` and the restriction of `ξ` lifts to no larger closed subscheme of
`Spec O_w`. The hypothesis is written out in full; its text is that of the statement
`EtaleLocus.GenericNoLargerLiftStatement` agreed between the executors of this task. This
module states the implication; it proves nothing. -/

universe u v

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

/-- The closed-subscheme form of Murre's Lemma 2 follows from the generic case: if, for every
noetherian `R`, every `F` satisfying the conditions, every étale `R`-algebra `R'`, ideal `𝔍`
and `ξ ∈ F(Spec (R'/𝔍))`, every point `y` of the étale locus of `ξ` lying over the nilradical
of `R` has an open neighbourhood `V` such that for all `w ∈ V` the ideal `𝔍 O_w` is nilpotent
and the restriction of `ξ` to `Spec (O_w/𝔍O_w)` lifts to no larger closed subscheme of
`Spec O_w` (`O_w` the localization of `R'` at the prime below `w`), then
`ClosedEtaleLocusOpenStatement` holds. -/
def ClosedOfGenericStatement : Prop :=
  (∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (𝔍 : Ideal R')
      (ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍))))
      (y : PrimeSpectrum (R' ⧸ 𝔍)), InfinitesimallyEtaleAt F ξ y →
      y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) ≤ nilradical R →
      ∃ V : Set (PrimeSpectrum (R' ⧸ 𝔍)), IsOpen V ∧ y ∈ V ∧
        ∀ w ∈ V, IsNilpotent (𝔍.map (algebraMap R' (Localization.AtPrime
            (w.asIdeal.comap (Ideal.Quotient.mk 𝔍))))) ∧
          NoLargerLift (Localization.AtPrime (w.asIdeal.comap (Ideal.Quotient.mk 𝔍))) ξ) →
    ClosedEtaleLocusOpenStatement.{u, v}

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
