import Langlands.GroupScheme.Rational.TorusVectorLinearization.Recoordinatize
import Langlands.GroupScheme.Rational.TorusVectorLinearization.CoordinateActionPolynomial

/-! # Natural coordinate transitions given by additive polynomials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

/-- The natural additive transition given by two mutually inverse tuples of additive
polynomials with coefficients in the ground field: a vector `x` goes to the values
`Φ i (x)`. -/
def NaturalCoordinateEquiv.ofPolynomials (Φ Q : Fin n → MvPolynomial (Fin n) k)
    (hΦ : ∀ i (B : Type u) [CommRing B] [Algebra k B] (x y : Fin n → B),
      aeval (x + y) (Φ i) = aeval x (Φ i) + aeval y (Φ i))
    (hQΦ : ∀ i, aeval Q (Φ i) = X i) (hΦQ : ∀ j, aeval Φ (Q j) = X j) :
    NaturalCoordinateEquiv k n where
  equiv A :=
    { toFun x i := aeval x (Φ i)
      invFun z j := aeval z (Q j)
      left_inv x := by
        funext j
        change aeval (fun i => aeval x (Φ i)) (Q j) = x j
        rw [← comp_aeval_apply, hΦQ, aeval_X]
      right_inv z := by
        funext i
        change aeval (fun j => aeval z (Q j)) (Φ i) = z i
        rw [← comp_aeval_apply, hQΦ, aeval_X]
      map_add' x y := by
        funext i
        exact hΦ i A x y }
  naturality f x := by
    funext i
    change aeval (fun j => f.hom (x j)) (Φ i) = f.hom (aeval x (Φ i))
    rw [comp_aeval_apply]

@[simp] theorem NaturalCoordinateEquiv.ofPolynomials_apply
    (Φ Q : Fin n → MvPolynomial (Fin n) k) (hΦ) (hQΦ) (hΦQ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : Fin n → A) :
    (NaturalCoordinateEquiv.ofPolynomials Φ Q hΦ hQΦ hΦQ).equiv A x =
      fun i => aeval x (Φ i) := rfl

@[simp] theorem NaturalCoordinateEquiv.ofPolynomials_symm_apply
    (Φ Q : Fin n → MvPolynomial (Fin n) k) (hΦ) (hQΦ) (hΦQ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (z : Fin n → A) :
    ((NaturalCoordinateEquiv.ofPolynomials Φ Q hΦ hQΦ hΦQ).equiv A).symm z =
      fun j => aeval z (Q j) := rfl

variable {H V : GroupScheme (Spec (CommRingCat.of k))} {a : AutomorphicAction H V}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}

/-- Natural coordinates are changed into natural coordinates that are scalar linear on
coefficient tests by mutually inverse additive polynomials `Φ`, `Q` over the ground
field, as soon as the coordinate action conjugated by `Φ` commutes with scalars. -/
theorem exists_isAffineLinear_of_polynomials (he : IsNaturalVectorCoordinates e)
    (Φ Q : Fin n → MvPolynomial (Fin n) k)
    (hΦ : ∀ i (B : Type u) [CommRing B] [Algebra k B] (x y : Fin n → B),
      aeval (x + y) (Φ i) = aeval x (Φ i) + aeval y (Φ i))
    (hQΦ : ∀ i, aeval Q (Φ i) = X i) (hΦQ : ∀ j, aeval Φ (Q j) = X j)
    (hlin : ∀ {B : Type u} [CommRing B] [Algebra k B] (t : Lie.AffinePoints H B)
      (c : B) (y : Fin n → B),
      (fun i => aeval (coordinateAction a e t (fun j => aeval (c • y) (Q j))) (Φ i)) =
        c • fun i => aeval (coordinateAction a e t (fun j => aeval y (Q j))) (Φ i)) :
    ∃ e' : ∀ W : Over (Spec (CommRingCat.of k)),
        (W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤)),
      IsNaturalVectorCoordinates e' ∧ IsAffineLinearVectorCoordinates a e' := by
  let Y := NaturalCoordinateEquiv.ofPolynomials Φ Q hΦ hQΦ hΦQ
  refine ⟨recoordinatize e Y, he.recoordinatize Y,
    isAffineLinearVectorCoordinates_recoordinatize Y ?_⟩
  intro A t c z
  exact hlin t c z

end Langlands.GroupScheme.RelativeRoot
