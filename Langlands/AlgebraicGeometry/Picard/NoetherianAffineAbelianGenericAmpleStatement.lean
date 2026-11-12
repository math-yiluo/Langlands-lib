import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic

/-! # Generic ampleness on abelian schemes over noetherian affine domains -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- On an abelian scheme over a noetherian affine integral base, a line bundle
whose canonical generic restriction is ample is ample on the total space. -/
def NoetherianAffineAbelianGenericAmpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))
    (L : LineBundle A.X.left),
    ((LineBundle.pullback (pullback.fst A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj L).IsAmple →
      L.IsAmple

end Langlands.AlgebraicGeometry.Picard
