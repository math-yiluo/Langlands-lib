import Langlands.Sheaf.CompactSoft

/-!
# Compact-germ lifting with a `c`-soft kernel

The proposition below isolates the finite-compact-cover lifting argument used in
the proof of Kashiwara–Schapira, *Sheaves on Manifolds*, Proposition 2.5.8.
Sections along a compact set are the published colimit of sections on its open
neighbourhoods.
-/

namespace Langlands.Sheaf.CompactSoft

universe u

/-- For a short exact sequence of module sheaves on a locally compact Hausdorff
space whose first term is `c`-soft, every germ of the third term along a compact
set lifts to a germ of the middle term. This is a derived intermediate lemma in
the finite-compact-cover proof of Kashiwara–Schapira, Proposition 2.5.8. -/
def CompactGermLiftingStatement : Prop :=
  ∀ (X : TopCat.{u}) [T2Space X] [LocallyCompactSpace X]
    (R : Type u) [CommRing R]
    (S : CategoryTheory.ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)),
    S.ShortExact → IsCSoft S.X₁ →
      ∀ (K : Set X), IsCompact K →
        Function.Surjective ((setSectionsFunctor R K).map S.g.hom)

end Langlands.Sheaf.CompactSoft
