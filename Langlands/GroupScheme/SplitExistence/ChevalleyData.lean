import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic

/-! # Integral Chevalley data for a reduced root datum

The algebraic input of the split existence construction: a free `ℤ`-module `ℤ^n` with a weight
basis whose weights generate `X`, divided-power root operators `e j k` for every root `j`
(integral matrices standing for `e_j^k / k!`), integral `SL₂`-homomorphisms for the simple roots,
Weyl conjugation and the integral commutator relations. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {n : ℕ}

/-- The truncated exponential `Σ_{k < n+1} s^k e_k` of a divided-power family of integral
`n × n` matrices, as a matrix over a commutative ring `R`. -/
def divExp (e : ℕ → Matrix (Fin n) (Fin n) ℤ) {R : Type*} [CommRing R] (s : R) :
    Matrix (Fin n) (Fin n) R :=
  ∑ k ∈ Finset.range (n + 1), s ^ k • (e k).map (Int.castRingHom R)

/-- The upper unitriangular matrix `[[1, s], [0, 1]]` of `SL₂(R)`. -/
def sl2Upper {R : Type*} [CommRing R] (s : R) : SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, s; 0, 1], by simp [det_fin_two]⟩

/-- The lower unitriangular matrix `[[1, 0], [s, 1]]` of `SL₂(R)`. -/
def sl2Lower {R : Type*} [CommRing R] (s : R) : SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; s, 1], by simp [det_fin_two]⟩

/-- The diagonal matrix `diag(t, t⁻¹)` of `SL₂(R)` for a unit `t`. -/
def sl2Diag {R : Type*} [CommRing R] (t : Rˣ) : SpecialLinearGroup (Fin 2) R :=
  ⟨!![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)], by simp [det_fin_two]⟩

/-- The Weyl element `[[0, 1], [-1, 0]]` of `SL₂(R)`. -/
def sl2Weyl {R : Type*} [CommRing R] : SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

/-- **Integral Chevalley data** for a root datum `P` with base `b`.

* `ℓ : X →+ ℤ` is positive on the simple roots (a dominant regular cocharacter).
* `wt : Fin n → X` are the weights of a basis of `ℤ^n`; they generate `X`.
* `e j k : Matrix (Fin n) (Fin n) ℤ` is the `k`-th divided power of the root operator of the
  root `j`: `e j 0 = 1`, `e j a * e j b = C(a+b, a) • e j (a+b)`, `e j k = 0` for `k > n`, it
  moves weight `μ` to `μ + k • root j`, and `e j 1` is nonzero modulo every prime.
* `φ i R : SL₂(R) →* GL_n(R)` for each simple root `i`, natural in `R`, sending the upper and
  lower unipotent matrices to the root exponentials of `i` and of `-i`, and `diag(t, t⁻¹)` to the
  diagonal matrix `t ^ ⟨wt c, coroot i⟩`.
* the Weyl element `φ i R (sl2Weyl)` moves weight `μ` to `s_i μ`;
* conjugation by the Weyl element `φ i R (sl2Weyl)` sends the exponential of a root `j` to that
  of `s_i j`, up to a sign `±1` of the parameter;
* commutator relations: for roots `j, j'` on which some `h : X →+ ℤ` is positive, over every
  commutative ring the group commutator of the exponentials is an ordered product of
  exponentials of roots `a • root j + c • root j'` with `a, c ≥ 1`. -/
structure ChevalleyData (P : RootDatum J X Y) (b : P.Base) where
  ℓ : X →+ ℤ
  ℓ_pos : ∀ i ∈ b.support, 0 < ℓ (P.root i)
  n : ℕ
  wt : Fin n → X
  closure_range_wt : AddSubgroup.closure (Set.range wt) = ⊤
  e : J → ℕ → Matrix (Fin n) (Fin n) ℤ
  e_zero : ∀ j, e j 0 = 1
  e_mul : ∀ j a c, e j a * e j c = ((a + c).choose a : ℤ) • e j (a + c)
  e_eq_zero : ∀ j k, n < k → e j k = 0
  e_weight : ∀ j k c d, e j k c d ≠ 0 → wt c = wt d + k • P.root j
  e_one_map_ne_zero : ∀ j (p : ℕ), p.Prime → (e j 1).map (Int.castRingHom (ZMod p)) ≠ 0
  φ : ∀ (_ : b.support) (R : Type u) [CommRing R], SpecialLinearGroup (Fin 2) R →* GL (Fin n) R
  φ_natural : ∀ (i : b.support) (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g : SpecialLinearGroup (Fin 2) R),
    ((φ i R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f =
      ((φ i S (g.map f) : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)
  φ_upper : ∀ (i : b.support) (R : Type u) [CommRing R] (s : R),
    ((φ i R (sl2Upper s) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = divExp (n := n) (e i) s
  φ_lower : ∀ (i : b.support) (R : Type u) [CommRing R] (s : R),
    ((φ i R (sl2Lower s) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      divExp (n := n) (e (P.reflectionPerm i i)) s
  φ_diag : ∀ (i : b.support) (R : Type u) [CommRing R] (t : Rˣ),
    ((φ i R (sl2Diag t) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      diagonal fun c => ((t ^ P.toLinearMap (wt c) (P.coroot i) : Rˣ) : R)
  weyl_weight : ∀ (i : b.support) (R : Type u) [CommRing R] (c d : Fin n),
    ((φ i R sl2Weyl : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) c d ≠ 0 →
      wt c = P.reflection i (wt d)
  weyl_conj : ∀ (i : b.support) (j : J), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ (R : Type u) [CommRing R] (s : R),
      ((φ i R sl2Weyl : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * divExp (n := n) (e j) s *
          ((φ i R sl2Weyl)⁻¹ : GL (Fin n) R) =
        divExp (n := n) (e (P.reflectionPerm i j)) ((ε : R) * s)
  commutator : ∀ (j j' : J) (h : X →+ ℤ), 0 < h (P.root j) → 0 < h (P.root j') →
    ∀ (R : Type u) [CommRing R] (s t : R), ∃ L : List (J × R),
      (∀ x ∈ L, ∃ a c : ℕ, 1 ≤ a ∧ 1 ≤ c ∧ P.root x.1 = a • P.root j + c • P.root j') ∧
      divExp (n := n) (e j) s * divExp (n := n) (e j') t * divExp (n := n) (e j) (-s) *
          divExp (n := n) (e j') (-t) = (L.map fun x => divExp (n := n) (e x.1) x.2).prod

end Langlands.GroupScheme.SplitExistence
