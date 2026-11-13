import Langlands.GroupScheme.Torus.CocharacterSplitting
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.PGroup

/-! # Rational points of tori have no nontrivial p-subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An injective realization of the actual rational points in a finite
product of units over a field extension. -/
structure TorusPointSplittingData (G : GroupScheme (Spec (CommRingCat.of k))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  indices : Type u
  [finite : Finite indices]
  embedding : rationalPoints G →* (indices → carrierˣ)
  injective : Function.Injective embedding

attribute [instance] TorusPointSplittingData.field TorusPointSplittingData.algebra
  TorusPointSplittingData.finite

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- Choose splitting coordinates and restrict them injectively to rational
points of an affine torus. -/
def IsTorus.pointSplittingData (hG : IsTorus G) : TorusPointSplittingData G := by
  exact Classical.choice (by
    obtain ⟨K, _, _, I, _, ⟨s⟩⟩ := hG
    let e₀ : rationalPoints G ≃* Lie.AffinePoints G k :=
      CocharacterSplitting.precompEquiv (ringTestSelfIso k)
    let f : k →ₐ[k] K := Algebra.ofId k K
    let eK : Lie.AffinePoints G K ≃* (I → Kˣ) :=
      (((CocharacterSplitting.precompEquiv (CocharacterSplitting.testIso K K)).trans
        (baseChangePointsEquiv (CocharacterSplitting.baseMap K) G
          (CocharacterSplitting.testScheme K K)).symm).trans
        (isoPointsEquiv s (CocharacterSplitting.testScheme K K))).trans
        (splitTorus.algebraPointsEquiv I K)
    exact ⟨{
      carrier := K
      indices := I
      embedding := eK.toMonoidHom.comp ((Lie.affineMap G f).comp e₀.toMonoidHom)
      injective := eK.injective.comp
        ((CocharacterDatum.affineMap_injective f (algebraMap k K).injective).comp e₀.injective) }⟩)

/-- A rational point of a torus killed by a power of the prime characteristic
is the identity. -/
theorem pow_prime_pow_eq_one_iff_of_isTorus (p : ℕ) [Fact p.Prime] [CharP k p]
    (hG : IsTorus G) (r : ℕ) (x : rationalPoints G) :
    x ^ p ^ r = 1 ↔ x = 1 := by
  constructor
  · intro hx
    let E := hG.pointSplittingData
    have : CharP E.carrier p :=
      charP_of_injective_algebraMap (algebraMap k E.carrier).injective p
    apply E.injective
    funext i
    apply Units.ext
    have hc := congrArg (fun y : rationalPoints G => (E.embedding y i : E.carrier)) hx
    have hr : (E.embedding x i : E.carrier) ^ (p ^ r) = 1 := by
      simpa only [map_pow, Pi.pow_apply, map_one, Pi.one_apply,
        Units.val_pow_eq_pow_val, Units.val_one] using hc
    have hd : (E.embedding x i : E.carrier) ^ 1 = 1 :=
      (ExpChar.pow_prime_pow_mul_eq_one_iff p r 1
        (E.embedding x i : E.carrier)).mp (by simpa only [mul_one] using hr)
    simpa only [pow_one, map_one, Pi.one_apply, Units.val_one] using hd
  · rintro rfl
    exact one_pow _

/-- Every `p`-subgroup of the actual rational-point group of a torus in
characteristic `p` is trivial. -/
theorem eq_bot_of_isPGroup_of_isTorus (p : ℕ) [Fact p.Prime] [CharP k p]
    (hG : IsTorus G) (H : Subgroup (rationalPoints G)) (hH : IsPGroup p H) :
    H = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, hr⟩ := hH.exists_pow_pow_eq_one (⟨x, hx⟩ : H)
  exact (pow_prime_pow_eq_one_iff_of_isTorus p hG r x).mp
    (congrArg (fun y : H => (y : rationalPoints G)) hr)

end Langlands.GroupScheme
