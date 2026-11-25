/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CocycleMonomialCoefficients
import WeilConjectures.FieldTheory.ProjectiveMatrixDescent

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

private def monomialLift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p : Equiv.Perm ι) (w : ι → Rˣ) :
    Matrix.GeneralLinearGroup ι R where
  val i j := if i = p j then (w j).val else 0
  inv i j := if p i = j then (w i).inv else 0
  val_inv := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (p.symm i)]
    · simp
    · intro k _ hk
      have hi : i ≠ p k := by
        intro h
        apply hk
        exact (p.symm_apply_apply k).symm.trans (congrArg p.symm h.symm)
      simp [hi]
    · simp
  inv_val := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (p i)]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [p.injective.eq_iff, hij]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp

private theorem monomialLift_mul_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p r : Equiv.Perm ι) (w v : ι → Rˣ) (f : R →+* R) :
    monomialLift p w * Matrix.GeneralLinearGroup.map f (monomialLift r v) =
      monomialLift (p * r) (fun j ↦ w (r j) * Units.map f (v j)) := by
  apply Units.ext
  ext i j
  change (∑ k, (if i = p k then (w k).val else 0) *
    f (if k = r j then (v j).val else 0)) =
      if i = (p * r) j then (w (r j) * Units.map f (v j)).val else 0
  rw [Finset.sum_eq_single (r j)]
  · simp [Equiv.Perm.mul_apply, ite_mul]
  · intro k _ hk
    simp [hk]
  · simp

private theorem monomialLift_scalar_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p : Equiv.Perm ι) (w : ι → Rˣ) (t : Rˣ) :
    monomialLift p (fun j ↦ t * w j) =
      Matrix.GeneralLinearGroup.scalar ι t * monomialLift p w := by
  apply Units.ext
  ext i j
  simp [monomialLift, Matrix.scalar, Matrix.diagonal_mul, mul_ite]

private theorem scalar_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (t : Rˣ) (M : Matrix ι ι R) :
    (Matrix.GeneralLinearGroup.scalar ι t).val * M *
      ((Matrix.GeneralLinearGroup.scalar ι t)⁻¹).val = M := by
  rw [show (Matrix.GeneralLinearGroup.scalar ι t).val * M =
    M * (Matrix.GeneralLinearGroup.scalar ι t).val from
      Matrix.scalar_comm _ (Commute.all _) M]
  rw [mul_assoc, (Matrix.GeneralLinearGroup.scalar ι t).mul_inv, mul_one]

private theorem scalar_mul_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (t : Rˣ) (B : Matrix.GeneralLinearGroup ι R)
    (M : Matrix ι ι R) :
    (Matrix.GeneralLinearGroup.scalar ι t * B).val * M *
      ((Matrix.GeneralLinearGroup.scalar ι t * B)⁻¹).val =
        B.val * M * (B⁻¹).val := by
  simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using
    scalar_conjugation t (B.val * M * (B⁻¹).val)

set_option linter.unusedVariables false in
/-- A prescribed continuous cocycle gives splitting and scalar-defect data.

Proof: write `G = Gal(Ksep/K)` and `c(g,h) = z(1,g,g*h)`. Equivariance and the
homogeneous cycle equation give
`c(g,h) * c(g*h,j) = g(c(h,j)) * c(g,h*j)`.
Since G is profinite, uncurry the iterated continuous cochain by the exponential law
for compact Hausdorff spaces. Its values are discrete, so c is locally constant with
finite image. A finite clopen cover gives an open normal subgroup N such that c is
constant on pairs of N-cosets. Shrink N to fix every value of c. Its fixed field L is
finite Galois over K, and c is inflated from a cocycle on Gamma = Gal(L/K) with values
in L-units.

On the L-space with basis indexed by Gamma define the monomial matrix B(g) by
`B(g) e_j = c(g,j) e_(g*j)`. Its nonzero coefficients are units, so it is invertible.
The cocycle equation gives `B(g) * g(B(h)) = c(g,h) * B(g*h)` on each basis vector.
No normalization is needed: the cocycle equation gives `c(1,j) = c(1,1)`, hence B(1)
is scalar. Thus `T_g(M) = B(g) * g(M) * B(g)^(-1)` is an actual semilinear action on
the matrix algebra, with T_1 the identity. Let A be its invariant K-subalgebra.

For completeness, finite Galois descent here is a vector-space argument. For any v
and a in L the sum over g of `g(a) * T_g(v)` is invariant. These invariant vectors
span over L: if an L-linear functional kills all such sums, linear independence of
the distinct field automorphisms forces it to kill T_1(v) = v for every v. Choose an
L-basis of invariant vectors. Invariant linear combinations have coefficients in K,
so it is also a K-basis of A. Therefore `L tensor_K A -> Matrix Gamma Gamma L` is an
algebra isomorphism. A is finite dimensional and simple: a nonzero ideal extends to
a nonzero ideal of the full matrix algebra, hence to the whole algebra; dimensions
then force the original ideal to be all of A. A central element becomes scalar after
extension, and invariance forces its scalar into K. Thus A is central simple.

Extend the splitting to Ksep and identify Gamma with Fin n for n = card Gamma > 0.
Inflate B along G -> Gamma; this is locally constant, and G acts on its coefficients
through Gamma. The monomial identity is exactly the required scalar-defect equation.
For a in A, invariance reads `g(e(1 tensor a)) = B(g)^(-1) * e(1 tensor a) * B(g)`,
which is the required descent equation. All objects are constructed from c.

Source: Stacks Project, Theorem 03R7, surjectivity argument, and Section 0DVG.
The explicit monomial matrices and descent argument fill in the construction omitted
by that sketch; this proof is given here.
(blueprint: new-crossed-product-for-cocycle). -/
theorem exists_crossedProduct_data_for_cocycle (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (A : CSA.{u, u} K) (n : ℕ) (hn : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)),
      IsLocallyConstant b ∧
      (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h)) := by
  obtain ⟨n, hn, p, w, hw, hdef⟩ := exists_cocycle_monomial_coefficients K z
  let b := fun g ↦ monomialLift (p g) (w g)
  have hb : IsLocallyConstant b := hw.comp (fun t ↦ monomialLift t.1 t.2)
  have hd : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
        b (g * h) := by
    intro g h
    change monomialLift (p g) (w g) *
      Matrix.GeneralLinearGroup.map g.toRingHom (monomialLift (p h) (w h)) = _
    rw [monomialLift_mul_map, ← p.map_mul]
    have hc : (fun j ↦ w g (p h j) * Units.map g.toRingHom (w h j)) =
        (fun j ↦ galoisUnitsCocycleValue K z g h * w (g * h) j) := by
      funext j
      exact hdef g h j
    rw [hc, monomialLift_scalar_mul]
  have h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M := by
    have hh := hd 1 1
    change b 1 * b 1 =
      Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z 1 1) * b 1 at hh
    have hb1 := mul_right_cancel hh
    intro M
    rw [hb1]
    exact scalar_conjugation _ M
  have hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val := by
    intro g h M
    calc
      _ = (b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h)).val *
          M.map (g * h) *
          ((b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h))⁻¹).val := by
        change (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g *
          ((b g)⁻¹).val = ((b g).val * (b h).val.map g) * M.map (g * h) *
            (((b h)⁻¹).val.map g * ((b g)⁻¹).val)
        simp only [Matrix.map_mul, Matrix.map_map, mul_assoc]
        rfl
      _ = _ := by
        rw [hd g h]
        exact scalar_mul_conjugation _ _ _
  obtain ⟨A, e, he⟩ := exists_CSA_of_matrix_descent_action K n hn b hb h1 hm
  exact ⟨A, n, hn, e, b, hb, he, hd⟩

end Field
