import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # The cubic polarization locus of a projectively embedded abelian scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- `L` is the cube of the diagonal Poincaré bundle of a polarization of degree `d²`,
up to the pullback of a line bundle from the base. -/
def ExistsCubicPolarization {S : Scheme.{u}} (P : Prerequisites.{u}) (d : ℕ)
    (A : AbelianScheme S) (L : LineBundle A.X.left) : Prop :=
  ∃ (W : DualWitness A) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam ∧ HasDegreeSquare lam d ∧
      ∃ N : LineBundle S,
        let D := poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)
        Nonempty (L ≅ LineBundle.tensor P.preservation
          ⟨tensorPow D.obj 3, tensorPow_isLocallyFreeRankOne _ D 3⟩
          ((LineBundle.pullback A.X.hom).obj N))

/-- For a projectively embedded abelian scheme, existence of a compatible polarization
of degree `d²` on a pullback is represented by an immersion of the base. -/
def CubicPolarizationLocusStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (A : AbelianScheme S) (m d : ℕ) (_hd : 0 < d)
    (i : A.X.left ⟶ RelativeProjectiveSpace S m),
    IsClosedImmersion i → i ≫ RelativeProjectiveSpace.toBase S m = A.X.hom →
      ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧
        ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
          (∃ t' : T ⟶ Z, t' ≫ j = t) ↔
            ExistsCubicPolarization P d ((baseChange t).obj A)
              ((LineBundle.pullback (pullback.fst A.X.hom t ≫ i)).obj
                (RelativeProjectiveSpace.twistOne S m))

end Langlands.AbelianScheme.PolarizedFiniteLevel
