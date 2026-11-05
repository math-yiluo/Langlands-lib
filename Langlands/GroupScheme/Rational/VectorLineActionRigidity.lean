import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.ElementaryOrbitLimit
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Rigidity of actions between one-dimensional vector groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace VectorLineAction

variable {k : Type u} [Field k]
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))

/-- The single affine coordinate, in the coefficient algebra itself. -/
def coord {A : Type u} [CommRing A] [Algebra k A] (v : Lie.AffinePoints V A) : A :=
  (vectorAffineCoordinates e A v).toAdd 0

/-- The affine point with the prescribed single coordinate. -/
def point {A : Type u} [CommRing A] [Algebra k A] (x : A) : Lie.AffinePoints V A :=
  (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd fun _ => x)

@[simp] theorem coord_point {A : Type u} [CommRing A] [Algebra k A] (x : A) :
    coord e (point e x) = x := by
  simp [coord, point]

theorem coord_injective {A : Type u} [CommRing A] [Algebra k A] :
    Function.Injective (coord e : Lie.AffinePoints V A → A) := by
  intro x y h
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [Subsingleton.elim j 0]
  exact h

@[simp] theorem point_coord {A : Type u} [CommRing A] [Algebra k A]
    (x : Lie.AffinePoints V A) : point e (coord e x) = x :=
  coord_injective e (coord_point e _)

@[simp] theorem coord_one {A : Type u} [CommRing A] [Algebra k A] :
    coord e (1 : Lie.AffinePoints V A) = 0 := by
  simp [coord]

@[simp] theorem point_zero {A : Type u} [CommRing A] [Algebra k A] :
    point e (0 : A) = 1 :=
  coord_injective e (by simp)

@[simp] theorem coord_inv {A : Type u} [CommRing A] [Algebra k A]
    (x : Lie.AffinePoints V A) : coord e x⁻¹ = -coord e x := by
  simp [coord]

@[simp] theorem point_neg {A : Type u} [CommRing A] [Algebra k A] (x : A) :
    point e (-x) = (point e x)⁻¹ :=
  coord_injective e (by simp)

variable {e}

theorem coord_map (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Lie.AffinePoints V A) :
    coord e (Lie.affineMap V f x) = f (coord e x) :=
  congrFun (he.vectorAffineCoordinates_naturality f x) 0

theorem map_point (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : A) :
    Lie.affineMap V f (point e x) = point e (f x) := by
  apply coord_injective e
  rw [coord_map he, coord_point, coord_point]

variable (b : AutomorphicAction U V)
    (eU : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))
    (eV : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))

/-- The given action written in the two single affine coordinates. -/
def actionCoord {A : Type u} [CommRing A] [Algebra k A] (s x : A) : A :=
  coord eV (b.act (point eU s) (point eV x))

@[simp] theorem actionCoord_zero_left {A : Type u} [CommRing A] [Algebra k A] (x : A) :
    actionCoord b eU eV 0 x = x := by
  simp [actionCoord]

@[simp] theorem actionCoord_zero_right {A : Type u} [CommRing A] [Algebra k A] (s : A) :
    actionCoord b eU eV s 0 = 0 := by
  simp [actionCoord]

@[simp] theorem actionCoord_neg_actionCoord
    {A : Type u} [CommRing A] [Algebra k A] (s x : A) :
    actionCoord b eU eV (-s) (actionCoord b eU eV s x) = x := by
  simp [actionCoord]

theorem actionCoord_map
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (s x : A) :
    f (actionCoord b eU eV s x) = actionCoord b eU eV (f s) (f x) := by
  rw [actionCoord, ← coord_map hV, b.affineAct_naturality,
    map_point hU, map_point hV]
  rfl

/-- The universal action polynomial, with the inner variable the acting point
and the outer variable the point acted on. -/
def actionPolynomial : k[X][X] :=
  actionCoord b eU eV (C X) X

private theorem linear_of_comp_eq_X
    {R : Type u} [CommRing R] [IsDomain R] {p q : R[X]}
    (hp : p.eval 0 = 0) (hq : q.eval 0 = 0) (hi : q.comp p = X) :
    ∃ c : R, IsUnit c ∧ p = C c * X := by
  have hd : q.natDegree * p.natDegree = 1 := by
    rw [← natDegree_comp, hi, natDegree_X]
  have hdeg : q.natDegree = 1 ∧ p.natDegree = 1 := by
    simpa only [mul_eq_one] using hd
  obtain ⟨c, hc, c₀, ep⟩ := natDegree_eq_one.mp hdeg.2
  obtain ⟨d, hd, d₀, eq⟩ := natDegree_eq_one.mp hdeg.1
  have hc₀ : c₀ = 0 := by simpa only [← ep, eval_add, eval_mul, eval_C,
    eval_X, mul_zero, zero_add] using hp
  have hd₀ : d₀ = 0 := by simpa only [← eq, eval_add, eval_mul, eval_C,
    eval_X, mul_zero, zero_add] using hq
  have ep' : p = C c * X := by simpa only [hc₀, C_0, add_zero] using ep.symm
  have eq' : q = C d * X := by simpa only [hd₀, C_0, add_zero] using eq.symm
  have hdc : d * c = 1 := by
    have h := congrArg (fun r : R[X] => r.coeff 1) hi
    simpa [ep', eq', mul_assoc, ← C_mul] using h
  exact ⟨c, IsUnit.of_mul_eq_one_right d hdc, ep'⟩

theorem inverse_actionPolynomial_comp
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV) :
    (actionCoord b eU eV (-C (X : k[X])) X).comp (actionPolynomial b eU eV) = X := by
  let f : k[X][X] →ₐ[k] k[X][X] :=
    (Polynomial.aeval (actionPolynomial b eU eV)).restrictScalars k
  have h := actionCoord_map b eU eV hU hV f (-C (X : k[X])) X
  have hs : f (-C (X : k[X])) = -C (X : k[X]) := by
    change Polynomial.aeval (actionPolynomial b eU eV) (-C (X : k[X])) = -C (X : k[X])
    simp
  have hx : f X = actionPolynomial b eU eV := by
    change Polynomial.aeval (actionPolynomial b eU eV) X = _
    simp
  change f (actionCoord b eU eV (-C (X : k[X])) X) = X
  rw [h, hs, hx, actionPolynomial, actionCoord_neg_actionCoord]

theorem actionPolynomial_eval_zero
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV) :
    (actionPolynomial b eU eV).eval 0 = 0 := by
  let f : k[X][X] →ₐ[k] k[X] :=
    (Polynomial.aeval (0 : k[X])).restrictScalars k
  have h := actionCoord_map b eU eV hU hV f (C X) X
  change f (actionCoord b eU eV (C X) X) = 0
  rw [h]
  have hx : f X = 0 := by
    change Polynomial.aeval (0 : k[X]) X = 0
    simp
  rw [hx, actionCoord_zero_right]

theorem actionPolynomial_eq_constant_mul_X
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV) :
    ∃ c : k, actionPolynomial b eU eV = C (C c) * X := by
  have hq : (actionCoord b eU eV (-C (X : k[X])) X : k[X][X]).eval 0 = 0 := by
    let f : k[X][X] →ₐ[k] k[X] :=
      (Polynomial.aeval (0 : k[X])).restrictScalars k
    have h := actionCoord_map b eU eV hU hV f (-C (X : k[X])) X
    change f (actionCoord b eU eV (-C (X : k[X])) X) = 0
    rw [h]
    have hx : f X = 0 := by
      change Polynomial.aeval (0 : k[X]) X = 0
      simp
    rw [hx, actionCoord_zero_right]
  obtain ⟨c, hc, hp⟩ := linear_of_comp_eq_X
    (actionPolynomial_eval_zero b eU eV hU hV) hq
    (inverse_actionPolynomial_comp b eU eV hU hV)
  obtain ⟨d, _, hd⟩ := Polynomial.isUnit_iff.mp hc
  exact ⟨d, by rw [← hd] at hp; exact hp⟩

theorem actionPolynomial_eq_X
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV) :
    actionPolynomial b eU eV = X := by
  obtain ⟨c, hc⟩ := actionPolynomial_eq_constant_mul_X b eU eV hU hV
  let f : k[X][X] →ₐ[k] k[X] := Polynomial.mapAlgHom (Polynomial.aeval (0 : k))
  have h := actionCoord_map b eU eV hU hV f (C X) X
  have hs : f (C X) = 0 := by simp [f]
  have hx : f X = X := by simp [f]
  have he : f (actionPolynomial b eU eV) = X := by
    change f (actionCoord b eU eV (C X) X) = X
    rw [h, hs, hx, actionCoord_zero_left]
  have hc1 : c = 1 := by
    rw [hc] at he
    have hcoeff := congrArg (fun p : k[X] => p.coeff 1) he
    simpa [f] using hcoeff
  simp [hc, hc1]

/-- On every coefficient algebra the original action fixes every affine point. -/
theorem actionCoord_eq
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV)
    {A : Type u} [CommRing A] [Algebra k A] (s x : A) :
    actionCoord b eU eV s x = x := by
  let f : k[X][X] →ₐ[k] A :=
    Polynomial.eval₂AlgHom (Polynomial.aeval s) x (fun _ => Commute.all _ _)
  have h := actionCoord_map b eU eV hU hV f (C X) X
  have hs : f (C X) = s := by
    change Polynomial.eval₂ (Polynomial.aeval s).toRingHom x (C X) = s
    simp
  have hx : f X = x := by
    change Polynomial.eval₂ (Polynomial.aeval s).toRingHom x X = x
    simp
  rw [hs, hx] at h
  have he := congrArg (fun p => f p) (actionPolynomial_eq_X b eU eV hU hV)
  exact h.symm.trans (he.trans hx)

theorem affineAct_eq
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV)
    {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints U A) (x : Lie.AffinePoints V A) : b.act s x = x := by
  apply coord_injective eV
  have h := actionCoord_eq b eU eV hU hV (coord eU s) (coord eV x)
  simpa only [actionCoord, point_coord] using h

/-- Every actual automorphic action between two vector groups of dimension one
is trivial, on every scheme over the field. -/
theorem eq_trivial
    (hU : IsNaturalVectorCoordinates eU) (hV : IsNaturalVectorCoordinates eV) :
    b = AutomorphicAction.trivial U V := by
  apply AutomorphicAction.eq_trivial_of_act_eq
  intro T s x
  apply OrbitLimit.hom_ext_of_algebraSpec
  intro A _ _ c
  rw [b.naturality]
  exact affineAct_eq b eU eV hU hV (c ≫ s) (c ≫ x)

end VectorLineAction

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme.AutomorphicAction

variable {k : Type u} [Field k]
    {U V : GroupScheme (Spec (CommRingCat.of k))}

/-- The intrinsic vector-group predicates suffice for action rigidity. -/
theorem eq_trivial_of_vectorLines (b : AutomorphicAction U V)
    (hU : RelativeRoot.IsVectorGroupOfDimension U 1)
    (hV : RelativeRoot.IsVectorGroupOfDimension V 1) :
    b = trivial U V := by
  obtain ⟨eU, hU⟩ := hU
  obtain ⟨eV, hV⟩ := hV
  exact RelativeRoot.VectorLineAction.eq_trivial b eU eV hU hV

end Langlands.GroupScheme.AutomorphicAction
