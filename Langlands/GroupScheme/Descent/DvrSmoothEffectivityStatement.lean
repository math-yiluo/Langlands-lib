import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Effective descent of smooth group schemes along extensions of discrete valuation rings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

/-- Let `R → R'` be a faithfully flat extension of discrete valuation rings in universe `u`.
Every actual Čech descent datum, along `Spec R' ⟶ Spec R`, on a smooth, separated
`R'`-group scheme of finite type has a solution: an `R`-group scheme whose base change is
identified with the given group compatibly with the datum. The descended group is smooth,
separated and of finite type over `R`. -/
def DvrSmoothGroupSchemeDescentStatement : Prop :=
  ∀ (R R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] (G : GroupScheme (Spec (CommRingCat.of R'))),
    Smooth G.X.hom → IsSeparated G.X.hom → LocallyOfFiniteType G.X.hom →
      QuasiCompact G.X.hom →
      ∀ D : Datum (Spec.map (CommRingCat.ofHom (algebraMap R R'))) G,
        ∃ s : Solution D, Smooth s.obj.X.hom ∧ IsSeparated s.obj.X.hom ∧
          LocallyOfFiniteType s.obj.X.hom ∧ QuasiCompact s.obj.X.hom

end Langlands.GroupScheme.Descent
