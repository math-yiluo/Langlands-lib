import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps

/-! # Murre's Lemma 2: the étale locus of a chart is open

Murre (Bourbaki exp. 294, Lemma 2) shows, under the noetherian induction hypothesis of his
proof of Proposition 2, that the set of points where a morphism `ξ : U → F` from an unramified,
separated `S`-scheme of finite type is étale is open. This module states it over the spectrum
of a noetherian ring, with étaleness at a point in the infinitesimal sense of SGA 3, XI 1.8
(`InfinitesimallyEtaleAt`). It proves nothing. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- Murre's Lemma 2 over an affine noetherian base. Let `R` be a noetherian ring and `F` a
presheaf on `Over (Spec R)` satisfying the conditions, whose base change to
`Spec 𝒪_{Spec R, s}` is representable (by a separated, locally of finite type, formally
unramified scheme) for every point `s`, and whose base change to every closed subscheme
`Spec (R/I)` with `I ≠ 0` is representable in the same way. Let `U` be an `Spec R`-scheme of
finite type, separated and formally unramified, and `ξ ∈ F(U)`. Then the set of points of `U`
at which `ξ : U → F` is infinitesimally étale is open. -/
def MurreEtaleLocusOpenStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    (∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F)) →
    (∀ I : Ideal R, I ≠ ⊥ →
      UnramifiedRepresentable (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F)) →
    ∀ (U : Over (Spec R)) (ξ : F.obj (op U)),
      LocallyOfFiniteType U.hom → QuasiCompact U.hom → IsSeparated U.hom →
      FormallyUnramified U.hom →
      IsOpen {y : U.left | InfinitesimallyEtaleAt F ξ y}

end Langlands.AlgebraicGeometry.UnramifiedFunctor
