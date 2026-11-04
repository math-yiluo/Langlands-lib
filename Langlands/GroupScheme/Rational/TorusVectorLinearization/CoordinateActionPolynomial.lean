import Langlands.GroupScheme.Rational.TorusVectorLinearization.AdditivePolynomialSupport
import Langlands.GroupScheme.Rational.VectorActionCharZero

/-! # Coordinate actions on vector groups are given by additive polynomials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (b : AutomorphicAction H V)
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- The action of an acting point on coordinate vectors over its coefficient algebra. -/
def coordinateAction {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) : (Fin n → A) →+ (Fin n → A) where
  toFun x := (vectorAffineCoordinates e A
    (b.act h ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)))).toAdd
  map_zero' := by
    simp only [ofAdd_zero, map_one, b.act_one, toAdd_one]
  map_add' x y := by
    simp only [ofAdd_add, map_mul, b.act_mul_right, toAdd_mul]

theorem coordinateAction_apply {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (x : Fin n → A) :
    coordinateAction b e h x = (vectorAffineCoordinates e A
      (b.act h ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)))).toAdd :=
  rfl

/-- The coordinate action of a point is computed from its action on points. -/
theorem coordinateAction_vectorAffineCoordinates {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (v : Lie.AffinePoints V A) :
    coordinateAction b e h (vectorAffineCoordinates e A v).toAdd =
      (vectorAffineCoordinates e A (b.act h v)).toAdd := by
  rw [coordinateAction_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

@[simp] theorem coordinateAction_one {A : Type u} [CommRing A] [Algebra k A]
    (x : Fin n → A) : coordinateAction b e (1 : Lie.AffinePoints H A) x = x := by
  rw [coordinateAction_apply, b.act_one_left, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem coordinateAction_mul {A : Type u} [CommRing A] [Algebra k A]
    (h h' : Lie.AffinePoints H A) (x : Fin n → A) :
    coordinateAction b e (h * h') x = coordinateAction b e h (coordinateAction b e h' x) := by
  simp only [coordinateAction_apply, b.act_mul_left, ofAdd_toAdd, MulEquiv.symm_apply_apply]

variable {e}

theorem vectorAffineCoordinates_symm_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Fin n → A) :
    Lie.affineMap V f ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)) =
      (vectorAffineCoordinates e B).symm (Multiplicative.ofAdd fun j => f (x j)) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- The coordinate action commutes with every change of coefficient algebra. -/
theorem coordinateAction_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (h : Lie.AffinePoints H A) (x : Fin n → A) :
    coordinateAction b e (Lie.affineMap H f h) (fun j => f (x j)) =
      fun j => f (coordinateAction b e h x j) := by
  rw [coordinateAction_apply, coordinateAction_apply,
    ← vectorAffineCoordinates_symm_naturality he f x,
    ← b.affineAct_naturality, he.vectorAffineCoordinates_naturality]

variable (e)

/-- The coordinate polynomials of an acting point: its action on the universal
coordinate vector, over the polynomial algebra of its coefficient algebra. -/
def coordinatePolynomials {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) : Fin n → MvPolynomial (Fin n) A :=
  coordinateAction b e
    (Lie.affineMap H (IsScalarTower.toAlgHom k A (MvPolynomial (Fin n) A)) h)
    MvPolynomial.X

variable {e}

/-- Over every algebra `C` over the coefficient algebra, the coordinate action of the
extended acting point is evaluation of the coordinate polynomials. -/
theorem coordinateAction_eq_aeval (he : IsNaturalVectorCoordinates e)
    {A C : Type u} [CommRing A] [Algebra k A] [CommRing C] [Algebra k C] [Algebra A C]
    [IsScalarTower k A C] (h : Lie.AffinePoints H A) (z : Fin n → C) :
    coordinateAction b e (Lie.affineMap H (IsScalarTower.toAlgHom k A C) h) z =
      fun i => MvPolynomial.aeval z (coordinatePolynomials b e h i) := by
  let g : MvPolynomial (Fin n) A →ₐ[k] C :=
    (MvPolynomial.aeval z : MvPolynomial (Fin n) A →ₐ[A] C).restrictScalars k
  have hg : g.comp (IsScalarTower.toAlgHom k A (MvPolynomial (Fin n) A)) =
      IsScalarTower.toAlgHom k A C := by
    ext a
    simp [g]
  have hz : (fun j => g (MvPolynomial.X j)) = z := by
    funext j
    simp [g]
  have h1 := coordinateAction_naturality b he g
    (Lie.affineMap H (IsScalarTower.toAlgHom k A (MvPolynomial (Fin n) A)) h)
    MvPolynomial.X
  rw [← Lie.affineMap_comp, hg, hz] at h1
  exact h1

/-- Over the coefficient algebra itself, the coordinate action is evaluation of the
coordinate polynomials. -/
theorem coordinateAction_eq_aeval_self (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A) (z : Fin n → A) :
    coordinateAction b e h z =
      fun i => MvPolynomial.aeval z (coordinatePolynomials b e h i) := by
  have hid : IsScalarTower.toAlgHom k A A = AlgHom.id k A := AlgHom.ext fun _ => rfl
  have h1 := coordinateAction_eq_aeval b he h z
  rwa [hid, Lie.affineMap_id] at h1

/-- The coordinate polynomials are additive on every algebra over the coefficient
algebra. -/
theorem coordinatePolynomials_additive (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A) (i : Fin n)
    (B : Type u) [CommRing B] [Algebra A B] (x y : Fin n → B) :
    MvPolynomial.aeval (x + y) (coordinatePolynomials b e h i) =
      MvPolynomial.aeval x (coordinatePolynomials b e h i) +
        MvPolynomial.aeval y (coordinatePolynomials b e h i) := by
  let _ : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx := congrFun (coordinateAction_eq_aeval b he h x) i
  have hy := congrFun (coordinateAction_eq_aeval b he h y) i
  have hxy := congrFun (coordinateAction_eq_aeval b he h (x + y)) i
  rw [← hx, ← hy, ← hxy, map_add, Pi.add_apply]

/-- The coordinate polynomials of an extended acting point are the images of the
coordinate polynomials. -/
theorem coordinatePolynomials_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (h : Lie.AffinePoints H A) (i : Fin n) :
    coordinatePolynomials b e (Lie.affineMap H f h) i =
      MvPolynomial.map (f : A →+* B) (coordinatePolynomials b e h i) := by
  let g : MvPolynomial (Fin n) A →ₐ[k] MvPolynomial (Fin n) B := MvPolynomial.mapAlgHom f
  have hg : g.comp (IsScalarTower.toAlgHom k A (MvPolynomial (Fin n) A)) =
      (IsScalarTower.toAlgHom k B (MvPolynomial (Fin n) B)).comp f := by
    ext a
    simp [g, MvPolynomial.algebraMap_eq]
  have hX : (fun j => g (MvPolynomial.X j)) = MvPolynomial.X := by
    funext j
    simp [g]
  have h1 := congrFun (coordinateAction_naturality b he g
    (Lie.affineMap H (IsScalarTower.toAlgHom k A (MvPolynomial (Fin n) A)) h)
    MvPolynomial.X) i
  rw [← Lie.affineMap_comp, hg, Lie.affineMap_comp, hX] at h1
  exact h1

/-- In characteristic `p`, the coordinate polynomials of every acting point are
`p`-polynomials: finite sums of scalar multiples of the powers `X j ^ p ^ s`. -/
theorem exists_coordinatePolynomials_eq_sum_pow (p : ℕ) [Fact p.Prime] [CharP k p]
    (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A) :
    ∃ (N : ℕ) (c : Fin n → Fin n → ℕ → A), ∀ i,
      coordinatePolynomials b e h i = ∑ j, ∑ s ∈ Finset.range N,
        MvPolynomial.C (c i j s) * MvPolynomial.X j ^ (p ^ s) := by
  have hpA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
  have hrep (i : Fin n) := AdditiveSupport.MvPolynomial.exists_eq_sum_pow_of_additive hpA
    (coordinatePolynomials b e h i) (coordinatePolynomials_additive b he h i)
  choose N₀ c hc using hrep
  refine ⟨∑ i, N₀ i, c, fun i => hc i _ ?_⟩
  exact Finset.single_le_sum (f := N₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- In characteristic `p`, the coordinate action of every acting point on every
algebra over its coefficient algebra is given by one `p`-polynomial matrix. -/
theorem exists_coordinateAction_eq_sum_pow (p : ℕ) [Fact p.Prime] [CharP k p]
    (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A) :
    ∃ (N : ℕ) (c : Fin n → Fin n → ℕ → A),
      ∀ (C : Type u) [CommRing C] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
        (z : Fin n → C) (i : Fin n),
        coordinateAction b e (Lie.affineMap H (IsScalarTower.toAlgHom k A C) h) z i =
          ∑ j, ∑ s ∈ Finset.range N, algebraMap A C (c i j s) * z j ^ (p ^ s) := by
  obtain ⟨N, c, hc⟩ := exists_coordinatePolynomials_eq_sum_pow b p he h
  refine ⟨N, c, fun C _ _ _ _ z i => ?_⟩
  rw [coordinateAction_eq_aeval b he h z]
  dsimp only
  rw [hc i]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, map_pow, MvPolynomial.aeval_X]

end Langlands.GroupScheme.RelativeRoot
