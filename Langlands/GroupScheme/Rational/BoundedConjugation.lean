import Langlands.GroupScheme.Rational.BoundedSplitTorusMaps
import Langlands.GroupScheme.PointCentralizer

/-! # A bounded conjugation grid forces split-torus commutation -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.BoundedTorusOrbits

variable {k : Type u} [Field k]
variable (I : Type u) [Fintype I] [DecidableEq I]
variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- The conjugation orbit of a rational point as a morphism of schemes. -/
def conjugationMap (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (x : rationalPoints G) : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ G.X :=
  j.hom.hom * (toUnit _ ≫ x) * j.hom.hom⁻¹

/-- A bounded conjugation orbit on the power grid is fixed under every rational
point of the split torus. -/
theorem commute_of_bounded_conjugation_grid
    (v : Valuation k (WithZero (Multiplicative ℤ))) (π : kˣ)
    (hπ : WithZero.log (v (π : k)) ≠ 0)
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (x : rationalPoints G)
    (B : Set (rationalPoints G))
    (hB : letI := ValuativeRel.ofValuation v; IsAlgebraicallyBounded k G.X B)
    (hgrid : ∀ n : Multiplicative (I → ℤ),
      rationalPoints.map j (tuplePoint I (powerTuple I π n)) * x *
        (rationalPoints.map j (tuplePoint I (powerTuple I π n)))⁻¹ ∈ B)
    (t : I → kˣ) : Commute (rationalPoints.map j (tuplePoint I t)) x := by
  let f := conjugationMap I j x
  have he (t : I → kˣ) : tuplePoint I t ≫ f =
      rationalPoints.map j (tuplePoint I t) * x *
        (rationalPoints.map j (tuplePoint I t))⁻¹ := by
    dsimp only [f, conjugationMap]
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    have hc : tuplePoint I t ≫ (toUnit _ ≫ x) = x := by
      rw [← Category.assoc, toUnit_unique (tuplePoint I t ≫ toUnit _) (𝟙 _),
        Category.id_comp]
    rw [hc]
    rfl
  have hf : ∀ s : AffineCoordinateRing k G.X, ∃ b : k, b ≠ 0 ∧
      ∀ n : Multiplicative (I → ℤ),
        v (rationalPointAlgebraHom k G.X (tuplePoint I (powerTuple I π n) ≫ f) s) ≤ v b := by
    intro s
    obtain ⟨b, hb, h⟩ := hB s
    refine ⟨b, hb, fun n => ?_⟩
    rw [he]
    exact h _ (hgrid n)
  have hc := tuplePoint_comp_eq_of_bounded I v π hπ f hf t
  rw [he, he] at hc
  have h1 : tuplePoint (k := k) I 1 = 1 := by simp [tuplePoint]
  rw [h1, map_one, one_mul, inv_one, mul_one] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

end Langlands.GroupScheme.BoundedTorusOrbits
