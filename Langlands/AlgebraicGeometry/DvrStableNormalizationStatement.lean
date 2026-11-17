import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Stable normal models of DVR schemes with smooth generic fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.AlgebraicGeometry

namespace DvrStableNormalization

/-- The product with `n + 1` factors, parenthesized on the left. -/
def positivePower {S : Scheme.{u}} (Y : Over S) : ℕ → Over S
  | 0 => Y
  | n + 1 => positivePower Y n ⊗ Y

/-- The consequences of stable normalization used for extending operations.
The lifting property is on actual morphisms over the DVR. -/
structure Model {R : Type u} [CommRing R] [IsDomain R]
    (X : Over (Spec (CommRingCat.of R))) where
  source : Over (Spec (CommRingCat.of R))
  map : source ⟶ X
  finite : IsFinite map.left
  surjective : Surjective map.left
  flat : Flat source.hom
  geometricallyReduced : GeometricallyReduced source.hom
  genericIso : IsIso
    ((Over.pullback (Spec.algebraMap R (FractionRing R))).map map)
  normal_powers : ∀ n, HasNormalStalks (positivePower source n).left
  normal_lift : ∀ (T : Over (Spec (CommRingCat.of R))),
    Flat T.hom → HasNormalStalks T.left →
    Function.Bijective (fun f : T ⟶ source => f ≫ map)

end DvrStableNormalization

/-- A flat separated finite-type DVR scheme with smooth actual generic fibre
has a stable normal model after a faithfully flat same-universe DVR extension. -/
def DvrStableNormalizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Over (Spec (CommRingCat.of R))),
    Flat X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    IsSeparated X.hom →
    Smooth ((Over.pullback (Spec.algebraMap R (FractionRing R))).obj X).hom →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R')
          (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
          Flat b ∧ Surjective b ∧
            Nonempty (DvrStableNormalization.Model ((Over.pullback b).obj X))

end Langlands.AlgebraicGeometry
