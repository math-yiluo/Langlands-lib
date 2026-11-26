import Langlands.Shimura.Coefficients.Algebraic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Regular highest weight of an algebraic representation of a similitude group

Kottwitz (1992), printed p. 658: the theorem on the `λ`-adic cohomology of his
Shimura varieties "becomes simpler and more useful when the highest weight of `ξ` is
regular". This module defines that condition for an algebraic representation of the
similitude group of an algebra with involution of the second kind, as in Kottwitz's
unitary groups: over a field of characteristic zero over which the algebra splits into
matrix factors exchanged in pairs by the involution, in matrix coordinates in which the
involution is the reversed transpose of the paired factor, a nonzero vector that is a
weight vector for the diagonal torus and is fixed by the upper unitriangular points
has a strictly dominant weight on each `GL_n` factor.
-/

noncomputable section

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A]
variable (σ : AlgebraInvolution R A)

/-- A splitting chart of `σ` over a field `K'` containing `R`: an isomorphism of
`K'`-algebras `K' ⊗_R A ≅ ∏_{j ∈ J} M_n(K')` and a map `c : J → J` such that the
extended involution reads `σ(x)_j = (x_{c j})` reversed-transposed, the entry `(k, l)`
of `σ(x)_j` being the entry `(n - 1 - l, n - 1 - k)` of `x_{c j}`. In these coordinates
the diagonal matrices and the upper triangular matrices of every factor are preserved
by `x ↦ σ(x)⁻¹`, so they cut out a maximal torus and a Borel subgroup of the similitude
group. -/
structure SplitChart (K' : Type u) [Field K'] [Algebra R K'] (J : Type) (n : ℕ) where
  /-- The matrix coordinates. -/
  equiv : K' ⊗[R] A ≃ₐ[K'] (J → Matrix (Fin n) (Fin n) K')
  /-- The conjugate factor. -/
  conj : J → J
  /-- The involution is the reversed transpose of the conjugate factor. -/
  involution_eq : ∀ (x : K' ⊗[R] A) (j : J) (k l : Fin n),
    equiv (σ.baseChange K' x) j k l = equiv x (conj j) (Fin.rev l) (Fin.rev k)

variable {σ}
variable {W : Type w} [AddCommGroup W] [Module R W]

/-- The highest weight of the algebraic representation `ρ` is regular. There are a
field `K' ⊇ R` of characteristic zero, a splitting chart of `σ` over `K'` with factors
indexed by a finite type `J` whose conjugation map has no fixed factor (the factors are
exchanged in pairs, as for an involution of the second kind), a nonzero vector
`w ∈ K' ⊗_R W`, and a weight `(μ, m)` with `μ : J → Fin n → ℤ`, such that

* every point `g` of the similitude group over `K'` whose coordinates are diagonal,
  `g_j = diag(t_{j,0}, …, t_{j,n-1})`, acts on `w` by `ν(g)^m ∏_{j,k} t_{j,k}^{μ_{j,k}}`,
  where `ν` is the multiplier;
* every point of multiplier `1` whose coordinates are upper unitriangular fixes `w`;
* for every `j`, the exponent of `t_{j,k}` on the points of multiplier `1`,
  `μ_{j,k} - μ_{c j, n-1-k}`, is strictly decreasing in `k`.

On the points of multiplier `1` the coordinates of the paired factor are determined
by `t_{c j, n-1-k} = t_{j,k}⁻¹`, which is why the regularity condition combines `μ_j`
and `μ_{c j}`. In characteristic zero the character of the torus determines these
combined exponents, since `K'ˣ` contains elements of infinite order. -/
def IsRegularHighestWeight (n : ℕ) (ρ : σ.AlgebraicRepresentation W) : Prop :=
  ∃ (K' : Type u) (_ : Field K') (_ : CharZero K') (_ : Algebra R K') (J : Type)
    (_ : Fintype J) (χ : SplitChart σ K' J n) (x : K' ⊗[R] W) (μ : J → Fin n → ℤ) (m : ℤ),
    (∀ j, χ.conj j ≠ j) ∧ x ≠ 0 ∧
    (∀ (g : σ.Points K') (t : J → Fin n → K'ˣ),
      (∀ j, χ.equiv (g.1.1 : K' ⊗[R] A) j = Matrix.diagonal (fun k => (t j k : K'))) →
        ρ.act K' g x =
          ((Points.multiplier σ K' g) ^ m * ∏ j, ∏ k, t j k ^ μ j k : K'ˣ) • x) ∧
    (∀ g : σ.Points K', Points.multiplier σ K' g = 1 →
      (∀ j, (χ.equiv (g.1.1 : K' ⊗[R] A) j).BlockTriangular id ∧
        ∀ k, χ.equiv (g.1.1 : K' ⊗[R] A) j k k = 1) →
        ρ.act K' g x = x) ∧
    ∀ j, StrictAnti (fun k : Fin n => μ j k - μ (χ.conj j) (Fin.rev k))

end Langlands.Shimura.AlgebraInvolution
