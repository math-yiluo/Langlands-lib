import Langlands.GroupScheme.SplitExistence.ChevalleyData

/-! # Integral `SL₂`-data for the simple roots

The intermediate data between the construction of the integral representation and the
construction of the root operators for all roots: a free `ℤ`-module `ℤ^n` with a weight basis
whose weights generate `X`, divided-power operators `E i k` and `F i k` for the simple roots `i`
and their negatives, integral `SL₂`-homomorphisms for the simple roots, and the relations
`[E i 1, F i 1] = H i`, `[E i 1, F i' 1] = 0` for `i ≠ i'`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

/-- **Integral `SL₂`-data for the simple roots** of a root datum `P` with base `b`.

* `ℓ : X →+ ℤ` is positive on the simple roots.
* `wt : Fin n → X` are the weights of a basis of `ℤ^n`; they generate `X`.
* `E i k` and `F i k` are the `k`-th divided powers of the root operators of the simple root `i`
  and of its negative: `E i 0 = 1`, `E i a * E i c = C(a+c, a) • E i (a+c)`, `E i k = 0` for
  `k > n`, `E i k` moves weight `μ` to `μ + k • root i`, `E i 1` is nonzero modulo every prime,
  and likewise for `F i` with `-root i`.
* `φ i R : SL₂(R) →* GL_n(R)` for each simple root `i`, natural in `R`, sending the upper and
  lower unipotent matrices to the exponentials of `E i` and `F i`, and `diag(t, t⁻¹)` to the
  diagonal matrix `t ^ ⟨wt c, coroot i⟩`; the Weyl element `φ i R sl2Weyl` moves weight `μ` to
  `s_i μ`.
* `E i 1 * F i 1 - F i 1 * E i 1` is the diagonal matrix `⟨wt c, coroot i⟩`, and `E i 1` and
  `F i' 1` commute for distinct simple roots `i ≠ i'`. -/
structure SimpleRootData (P : RootDatum J X Y) (b : P.Base) where
  ℓ : X →+ ℤ
  ℓ_pos : ∀ i ∈ b.support, 0 < ℓ (P.root i)
  n : ℕ
  wt : Fin n → X
  closure_range_wt : AddSubgroup.closure (Set.range wt) = ⊤
  E : b.support → ℕ → Matrix (Fin n) (Fin n) ℤ
  F : b.support → ℕ → Matrix (Fin n) (Fin n) ℤ
  E_zero : ∀ i, E i 0 = 1
  F_zero : ∀ i, F i 0 = 1
  E_mul : ∀ i a c, E i a * E i c = ((a + c).choose a : ℤ) • E i (a + c)
  F_mul : ∀ i a c, F i a * F i c = ((a + c).choose a : ℤ) • F i (a + c)
  E_eq_zero : ∀ i k, n < k → E i k = 0
  F_eq_zero : ∀ i k, n < k → F i k = 0
  E_weight : ∀ i k c d, E i k c d ≠ 0 → wt c = wt d + k • P.root i
  F_weight : ∀ i k c d, F i k c d ≠ 0 → wt c + k • P.root i = wt d
  E_one_map_ne_zero : ∀ i (p : ℕ), p.Prime → (E i 1).map (Int.castRingHom (ZMod p)) ≠ 0
  F_one_map_ne_zero : ∀ i (p : ℕ), p.Prime → (F i 1).map (Int.castRingHom (ZMod p)) ≠ 0
  φ : ∀ (_ : b.support) (R : Type u) [CommRing R], SpecialLinearGroup (Fin 2) R →* GL (Fin n) R
  φ_natural : ∀ (i : b.support) (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g : SpecialLinearGroup (Fin 2) R),
    ((φ i R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f =
      ((φ i S (g.map f) : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)
  φ_upper : ∀ (i : b.support) (R : Type u) [CommRing R] (s : R),
    ((φ i R (sl2Upper s) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = divExp (n := n) (E i) s
  φ_lower : ∀ (i : b.support) (R : Type u) [CommRing R] (s : R),
    ((φ i R (sl2Lower s) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = divExp (n := n) (F i) s
  φ_diag : ∀ (i : b.support) (R : Type u) [CommRing R] (t : Rˣ),
    ((φ i R (sl2Diag t) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      diagonal fun c => ((t ^ P.toLinearMap (wt c) (P.coroot i) : Rˣ) : R)
  weyl_weight : ∀ (i : b.support) (R : Type u) [CommRing R] (c d : Fin n),
    ((φ i R sl2Weyl : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) c d ≠ 0 →
      wt c = P.reflection i (wt d)
  E_F_same : ∀ i, E i 1 * F i 1 - F i 1 * E i 1 =
    diagonal fun c => P.toLinearMap (wt c) (P.coroot i)
  E_F_comm : ∀ i i' : b.support, i ≠ i' → E i 1 * F i' 1 = F i' 1 * E i 1

end Langlands.GroupScheme.SplitExistence
