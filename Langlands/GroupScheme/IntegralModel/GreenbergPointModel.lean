import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Smooth affine residue-field models of congruence-level points

A points-level consequence of the Greenberg functor (KP Theorem A.4.19): at
each positive level `n`, the group `X(R/𝔪ⁿ)` of a smooth affine group scheme
over a DVR with algebraically closed residue field `k` is the group of
`k`-points of a smooth affine `k`-group, compatibly with homomorphisms into
`X`, and geometrically connected sources give geometrically connected models.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

/-- **Greenberg models of congruence-level points (from KP Theorem A.4.19).**
Let `R` be a DVR with algebraically closed residue field `k`, let `n` be a
positive level and let `X` be a smooth affine group scheme over `Spec R`.
Then there is a smooth affine `k`-group `G` and a group isomorphism
`X(R/𝔪ⁿ) ≃* G(k)` such that for every smooth affine group scheme `Z` over
`Spec R` and every homomorphism `h : Z ⟶ X` there are a smooth affine
`k`-group `G_Z`, a group isomorphism `Z(R/𝔪ⁿ) ≃* G_Z(k)` and a homomorphism
`g : G_Z ⟶ G` making the square with the level-`n` map of `h` commute on
points, where `G_Z` is geometrically connected whenever `Z` is. -/
def GreenbergPointModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (n : ℕ+)
    (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom],
    Smooth X.X.hom →
    ∃ (G : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (eX : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj X) ≃*
        rationalPoints G),
      IsAffineHom G.X.hom ∧ Smooth G.X.hom ∧
      ∀ (Z : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom Z.X.hom],
        Smooth Z.X.hom → ∀ h : Z ⟶ X,
        ∃ (GZ : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
          (eZ : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj Z) ≃*
            rationalPoints GZ)
          (g : GZ ⟶ G),
          IsAffineHom GZ.X.hom ∧ Smooth GZ.X.hom ∧
          (∀ z, eX (rationalPoints.map ((GroupScheme.baseChange (congruenceBaseMap R n)).map h)
              z) = rationalPoints.map g (eZ z)) ∧
          (GeometricallyConnected Z.X.hom → GeometricallyConnected GZ.X.hom)

end Langlands.GroupScheme.IntegralModel
