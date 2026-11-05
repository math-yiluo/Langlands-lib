import Langlands.GroupScheme.SplitExistence.ChevalleyData

/-! # Integral Chevalley data with Lie relations

`ChevalleyLieData P b` has the same fields as `ChevalleyData P b`, with identical names and
types, except that the group commutator relations are replaced by the integral Lie relations
`lie_e_e` among the root operators `e j 1`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

/-- **Integral Chevalley data with Lie relations** for a root datum `P` with base `b`.

* `ℓ : X →+ ℤ` is positive on the simple roots.
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
* Lie relations: for roots `j, j'` with `root j' ≠ -root j`, the commutator
  `[e j 1, e j' 1]` is either zero or an integer multiple of `e k 1` for a root `k` with
  `root k = root j + root j'`. -/
structure ChevalleyLieData (P : RootDatum J X Y) (b : P.Base) where
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
  lie_e_e : ∀ j j' : J, P.root j' ≠ -P.root j →
    e j 1 * e j' 1 - e j' 1 * e j 1 = 0 ∨
      ∃ (k : J) (c : ℤ), P.root k = P.root j + P.root j' ∧
        e j 1 * e j' 1 - e j' 1 * e j 1 = c • e k 1

end Langlands.GroupScheme.SplitExistence
