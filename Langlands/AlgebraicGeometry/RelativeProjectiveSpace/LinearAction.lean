import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.AffineComparison
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearAction

/-! # Projective linear actions over arbitrary scheme bases -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [CommRing K] {X S T : Scheme.{u}} {n : ℕ}

/-- Projection from relative projective space to polynomial projective space over
a coefficient ring of the base scheme. -/
def toPolynomial (n : ℕ) (a : S ⟶ Spec (CommRingCat.of K)) :
    RelativeProjectiveSpace S n ⟶ ProjectiveSpace K n :=
  map n a ≫ (affineComparisonIso K n).inv

@[reassoc (attr := simp)]
lemma toPolynomial_toSpec (a : S ⟶ Spec (CommRingCat.of K)) :
    toPolynomial n a ≫ projectiveSpaceToSpec K n = toBase S n ≫ a := by
  simp [toPolynomial]

@[reassoc (attr := simp)]
lemma toPolynomial_toIntegral (a : S ⟶ Spec (CommRingCat.of K)) :
    toPolynomial n a ≫ polynomialToIntegral K n = toIntegral S n := by
  simp [toPolynomial]

@[reassoc (attr := simp)]
lemma map_toPolynomial (a : S ⟶ Spec (CommRingCat.of K)) (f : T ⟶ S) :
    map n f ≫ toPolynomial n a = toPolynomial n (f ≫ a) := by
  simp [toPolynomial, ← Category.assoc, ← map_comp]

/-- Lift a compatible base map and a map to polynomial projective space. -/
def liftOverPolynomial (n : ℕ) (a : S ⟶ Spec (CommRingCat.of K)) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace K n)
    (_w : q ≫ projectiveSpaceToSpec K n = p ≫ a) :
    X ⟶ RelativeProjectiveSpace S n :=
  lift n p (q ≫ polynomialToIntegral K n)

@[reassoc (attr := simp)]
lemma liftOverPolynomial_toBase (a : S ⟶ Spec (CommRingCat.of K)) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace K n)
    (w : q ≫ projectiveSpaceToSpec K n = p ≫ a) :
    liftOverPolynomial n a p q w ≫ toBase S n = p := by
  simp [liftOverPolynomial]

@[reassoc (attr := simp)]
lemma liftOverPolynomial_toPolynomial (a : S ⟶ Spec (CommRingCat.of K)) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace K n)
    (w : q ≫ projectiveSpaceToSpec K n = p ≫ a) :
    liftOverPolynomial n a p q w ≫ toPolynomial n a = q := by
  apply (cancel_mono (affineComparisonIso K n).hom).mp
  simp only [toPolynomial, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply hom_ext
  · simp [liftOverPolynomial, w]
  · simp [liftOverPolynomial]

/-- The base and polynomial projections determine an actual morphism uniquely. -/
lemma hom_ext_toPolynomial (a : S ⟶ Spec (CommRingCat.of K))
    {f g : X ⟶ RelativeProjectiveSpace S n}
    (hbase : f ≫ toBase S n = g ≫ toBase S n)
    (hpoly : f ≫ toPolynomial n a = g ≫ toPolynomial n a) : f = g := by
  apply hom_ext hbase
  simpa only [Category.assoc, toPolynomial_toIntegral] using
    congrArg (fun h ↦ h ≫ polynomialToIntegral K n) hpoly

/-- The actual relative projective action of an invertible coefficient linear map. -/
def linearAction (a : S ⟶ Spec (CommRingCat.of K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    RelativeProjectiveSpace S n ⟶ RelativeProjectiveSpace S n :=
  liftOverPolynomial n a (toBase S n)
    (toPolynomial n a ≫ ProjectiveSpace.linearAction K n e) (by
      simp only [Category.assoc, ProjectiveSpace.linearAction_comp_toSpec,
        toPolynomial_toSpec])

@[reassoc (attr := simp)]
lemma linearAction_toBase (a : S ⟶ Spec (CommRingCat.of K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    linearAction a e ≫ toBase S n = toBase S n := by
  simp [linearAction]

@[reassoc (attr := simp)]
lemma linearAction_toPolynomial (a : S ⟶ Spec (CommRingCat.of K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    linearAction a e ≫ toPolynomial n a =
      toPolynomial n a ≫ ProjectiveSpace.linearAction K n e := by
  exact liftOverPolynomial_toPolynomial a _ _ _

@[simp]
lemma linearAction_refl (a : S ⟶ Spec (CommRingCat.of K)) :
    linearAction (n := n) a (LinearEquiv.refl K _) = 𝟙 _ := by
  apply hom_ext_toPolynomial a <;> simp

/-- The relative action has the same covariant composition law as the
coefficient-space action. -/
lemma linearAction_comp (a : S ⟶ Spec (CommRingCat.of K))
    (e f : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    linearAction a e ≫ linearAction a f = linearAction a (e.trans f) := by
  apply hom_ext_toPolynomial a
  · simp
  · simp only [Category.assoc, linearAction_toPolynomial,
      linearAction_toPolynomial_assoc, ProjectiveSpace.linearAction_comp]

/-- The invertible relative coordinate change as an actual scheme isomorphism. -/
def linearActionIso (a : S ⟶ Spec (CommRingCat.of K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    RelativeProjectiveSpace S n ≅ RelativeProjectiveSpace S n where
  hom := linearAction a e
  inv := linearAction a e.symm
  hom_inv_id := by rw [linearAction_comp, LinearEquiv.self_trans_symm, linearAction_refl]
  inv_hom_id := by rw [linearAction_comp, LinearEquiv.symm_trans_self, linearAction_refl]

/-- Coefficient linear actions commute with arbitrary change of scheme base
over the same coefficient ring. -/
lemma map_linearAction (a : S ⟶ Spec (CommRingCat.of K)) (f : T ⟶ S)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    map n f ≫ linearAction a e = linearAction (f ≫ a) e ≫ map n f := by
  apply hom_ext_toPolynomial a <;> simp

/-- Scalar units act trivially on the whole relative projective scheme. -/
@[simp]
lemma linearAction_smulOfUnit (a : S ⟶ Spec (CommRingCat.of K)) (c : Kˣ) :
    linearAction (n := n) a (LinearEquiv.smulOfUnit c) = 𝟙 _ := by
  apply hom_ext_toPolynomial a <;>
    simp [ProjectiveSpace.linearAction_smulOfUnit]

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
