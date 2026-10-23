import Langlands.Cohomology.Tate.OrdinaryCupDefinitions
import Langlands.Cohomology.Tate.CupDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

universe u

open CategoryTheory
open scoped MonoidalCategory

namespace Langlands.Tate

/-- The two connecting-map signs for the actual ordinary tensor cup. -/
def OrdinaryCupBoundaryLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G],
    (∀ (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
      (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
      (p q : ℕ) (a : groupCohomology S.X₃ p) (b : groupCohomology B q),
      ordinaryCup (tensorPairing S.X₁ B) (p + 1) q
          (groupCohomology.δ hS p (p + 1) rfl a) b =
        (eqToIso (congrArg (groupCohomology (S.X₁ ⊗ B))
          (show (p + q) + 1 = (p + 1) + q by omega))).hom
            (groupCohomology.δ hB (p + q) ((p + q) + 1) rfl
              (ordinaryCup (tensorPairing S.X₃ B) p q a b))) ∧
    (∀ (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
      (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
      (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology S.X₃ q),
      ordinaryCup (tensorPairing A S.X₁) p (q + 1) a
          (groupCohomology.δ hS q (q + 1) rfl b) =
        (-1 : R) ^ p •
          (eqToIso (congrArg (groupCohomology (A ⊗ S.X₁))
            (show (p + q) + 1 = p + (q + 1) by omega))).hom
              (groupCohomology.δ hA (p + q) ((p + q) + 1) rfl
                (ordinaryCup (tensorPairing A S.X₃) p q a b)))

end Langlands.Tate
