import Langlands.AlgebraicGeometry.HQuasiProjective
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Effective quotients by flat proper equivalence relations on quasi-projective schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `A` be a noetherian ring, `Z` an H-quasi-projective scheme over `Spec A`, and
`s t : R ⟶ Z` a pair of morphisms over `Spec A` such that the induced morphism
`R ⟶ Z ×_A Z` is a monomorphism and its image on `T`-points is an equivalence relation for
every scheme `T`. If `s` is flat and proper, then there are an H-quasi-projective scheme `Q`
over `Spec A` and a flat, surjective, proper morphism `π : Z ⟶ Q` over `Spec A`, locally of
finite presentation, such that `R` together with `s` and `t` is the fibre product `Z ×_Q Z`. -/
def FlatProperEquivalenceRelationQuotientStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] {Z R : Scheme.{u}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (s t : R ⟶ Z) (h : s ≫ p = t ≫ p),
    IsHQuasiProjective p → Mono (pullback.lift s t h) →
    (∀ T : Scheme.{u},
      Equivalence fun x y : T ⟶ Z => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) →
    Flat s → IsProper s →
      ∃ (Q : Scheme.{u}) (q : Q ⟶ Spec (CommRingCat.of A)) (π : Z ⟶ Q),
        IsHQuasiProjective q ∧ π ≫ q = p ∧
          Flat π ∧ Surjective π ∧ IsProper π ∧ LocallyOfFinitePresentation π ∧
          IsPullback s t π π

end Langlands.AlgebraicGeometry
