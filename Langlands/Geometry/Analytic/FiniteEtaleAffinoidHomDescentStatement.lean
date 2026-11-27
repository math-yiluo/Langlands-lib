import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.SmallAffinoidSpectrum
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Descent of analytic morphisms along finite étale covers of affinoid spaces -/

universe u v

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Existence of descent of analytic morphisms along a finite étale, spectrum-surjective map
of affinoid spaces: for a finite Banach, algebraically finite étale map `f : A → B` of
presented affinoid algebras that is surjective on Banach spectra, every morphism
`g : M(B) ⟶ T` to an analytic space `T` that equalizes all pairs of morphisms identified by
`M(f) : M(B) ⟶ M(A)` factors as `M(f) ≫ h`. This is condition (2) of Berkovich 1993,
Lemma 4.1.1, for the presheaf represented by `T`, along finite étale maps (Berkovich 1993,
Proposition 4.1.3 and Remark 4.1.5; Conrad–Temkin 2009, Theorem 4.1.2). -/
def FiniteEtaleAffinoidHomDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B),
    f.IsFiniteBanach → f.AlgebraicallyFiniteEtale →
    Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) →
    ∀ (T : LocalizedCategory.{u, v, v} (K := K))
      (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶ T),
      (∀ (Z : LocalizedCategory.{u, v, v} (K := K))
          (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
          a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
              b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) →
            a ≫ g = b ≫ g) →
      ∃ h : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} A) ⟶ T,
        localizationFunctor.map (SmallAffinoidSpectrum.map f) ≫ h = g

end Langlands.Analytic.SaturatedAtlasPresentation
