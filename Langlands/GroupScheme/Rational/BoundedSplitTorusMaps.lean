import Langlands.GroupScheme.Rational.BoundedTorusOrbits
import Langlands.GroupScheme.Dynamic.AffineChart
import Langlands.GroupScheme.GaloisPointRational

/-! # Constancy of bounded maps on split-torus power grids -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.BoundedTorusOrbits

open splitTorus GaloisPointComparison Dynamic.AffineChart

variable {k : Type u} [Field k]
variable (I : Type u) [Fintype I] [DecidableEq I]

/-- The rational split-torus point with the specified field-unit coordinates. -/
def tuplePoint (t : I → kˣ) : rationalPoints (splitTorus (Spec (CommRingCat.of k)) I) :=
  (rationalCoeffEquiv k _).symm ((algebraPointsEquiv I k).symm t)

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

theorem pointRing_rationalCoeffEquiv_symm (x : Lie.AffinePoints G k) :
    pointRing ((rationalCoeffEquiv k G).symm x) = pointRing x := by
  have h := rationalCoeffEquiv_left k G ((rationalCoeffEquiv k G).symm x)
  simp only [MulEquiv.apply_symm_apply] at h
  dsimp only [pointRing]
  rw [← h]

theorem rationalPointAlgebraHom_eq_pointRing (x : rationalPoints G)
    (s : AffineCoordinateRing k G.X) :
    rationalPointAlgebraHom k G.X x s = pointRing x s := by
  have h : CommRingCat.ofHom (rationalPointAlgebraHom k G.X x).toRingHom = pointRing x := by
    apply Spec.map_injective
    rw [specMap_pointRing]
    change Spec.map (CommRingCat.ofHom
      (affineSchemePointEquiv k G.X k (rationalPointEquiv k G.X x)).toAlgHom.toRingHom) = _
    rw [affineSchemePointEquiv_spec, rationalPointEquiv_left]
  exact congrArg (fun f : Γ(G.X.left, ⊤) ⟶ CommRingCat.of k => f s) h

/-- Evaluation of an affine map on unit tuples evaluates its universal Laurent coordinates. -/
theorem pointRing_tuplePoint (f : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ G.X)
    (t : I → kˣ) (s : Γ(G.X.left, ⊤)) :
    pointRing (tuplePoint I t ≫ f) s =
      evaluateUnits (R := CommRingCat.of k) I t
        (pointRing (splitTorus.universalPoint (R := CommRingCat.of k) I ≫ f) s) := by
  have h : pointRing (tuplePoint I t ≫ f) =
      pointRing ((algebraPointsEquiv I k).symm t ≫ f) := by
    have hl : ((algebraPointsEquiv I k).symm t).left = (tuplePoint I t).left := by
      simpa only [tuplePoint, MulEquiv.apply_symm_apply] using
        rationalCoeffEquiv_left k _ (tuplePoint I t)
    dsimp only [pointRing, Over.comp_left]
    rw [← hl]
  rw [h, ← universalPoint_evaluateUnits I t, Lie.affineMap_apply, Category.assoc,
    pointRing_comp]
  change (pointRing (splitTorus.universalPoint I ≫ f) ≫
    Spec.preimage (Spec.map (CommRingCat.ofHom (evaluateUnits I t).toRingHom))) s = _
  rw [Spec.preimage_map]
  rfl

/-- If each regular function is uniformly bounded on a power grid, every rational
point of the split torus has the same image. -/
theorem tuplePoint_comp_eq_of_bounded
    (v : Valuation k (WithZero (Multiplicative ℤ))) (π : kˣ)
    (hπ : WithZero.log (v (π : k)) ≠ 0)
    (f : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ G.X)
    (hf : ∀ s : AffineCoordinateRing k G.X, ∃ b : k, b ≠ 0 ∧
      ∀ n : Multiplicative (I → ℤ),
        v (rationalPointAlgebraHom k G.X (tuplePoint I (powerTuple I π n) ≫ f) s) ≤ v b)
    (t : I → kˣ) : tuplePoint I t ≫ f = tuplePoint I 1 ≫ f := by
  apply hom_ext_of_pointRing
  ext s
  let p := pointRing (splitTorus.universalPoint (R := CommRingCat.of k) I ≫ f) s
  have hp : p = AddMonoidAlgebra.single 0 (p.coeff 0) := by
    apply eq_constant_of_bounded I v π hπ
    obtain ⟨b, hb, h⟩ := hf s
    refine ⟨b, hb, fun n => ?_⟩
    have hn := h n
    rw [rationalPointAlgebraHom_eq_pointRing, pointRing_tuplePoint] at hn
    exact hn
  rw [pointRing_tuplePoint, pointRing_tuplePoint]
  change evaluateUnits I t p = evaluateUnits I 1 p
  rw [hp]
  rw [evaluateUnits_single, evaluateUnits_single]
  simp [exponentValue]

end Langlands.GroupScheme.BoundedTorusOrbits
