import Langlands.Representation.Archimedean.Kostant.Center

/-!
# The coadjoint derivations of the symbol ring and the orbit statement

For `x ∈ L = ∏ᵢ 𝔤𝔩_{n i}(K)` the derivation `coadDer x` of `K[X_c]` sends the variable
`X_c = ξ(E_c)` to `ξ⁅x, E_c⁆`; hence `coadDer x (ξ y) = ξ⁅x, y⁆` for all `y`, so commutators with
`x` act on symbols through `coadDer x`. Evaluating polynomials at a tuple of matrices `Y` by
`X ⟨i, p, q⟩ ↦ Y i p q`, `coadDer (E i a b)` is the vector field `Y ↦ [E i b a, Y]` along the
conjugation `Y ↦ (1 + s E_ba) Y (1 - s E_ba)`.

`OrbitVanishingStatement` says: a space of polynomials stable under the derivations
`coadDer (E i a b)`, `a ≠ b`, all of whose elements vanish at the regular nilpotent tuple with
nonzero superdiagonal entries `c i p`, consists of polynomials vanishing at every tuple of
nilpotent matrices.
-/

noncomputable section

set_option autoImplicit false

-- Entries of tuples of matrices are applied through the `Matrix` definition.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable (K : Type*) [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

/-- The coadjoint derivation: `X_c ↦ ξ⁅x, E_c⁆ = ∑_d ⁅x, E_c⁆_d X_d`. -/
def coadDer (x : GLProd K n) :
    Derivation K (MvPolynomial (Coord n) K) (MvPolynomial (Coord n) K) :=
  mkDerivation K fun c => ∑ d : Coord n, ⁅x, unit K n c.1 c.2.1 c.2.2⁆ d.1 d.2.1 d.2.2 • X d

theorem coadDer_X (x : GLProd K n) (c : Coord n) :
    coadDer K n x (X c) = ∑ d : Coord n, ⁅x, unit K n c.1 c.2.1 c.2.2⁆ d.1 d.2.1 d.2.2 • X d :=
  mkDerivation_X _ _ _

variable [CharZero K]

omit [CharZero K] in
theorem glSymbol_ξ_apply (y : GLProd K n) :
    (glSymbol K n).ξ y = ∑ d : Coord n, y d.1 d.2.1 d.2.2 • (X d : MvPolynomial (Coord n) K) := by
  rw [AssocSymbol.symbolData_ξ]
  simp only [glBasis_repr]

omit [CharZero K] in
theorem coadDer_ξ (x y : GLProd K n) :
    coadDer K n x ((glSymbol K n).ξ y) = (glSymbol K n).ξ ⁅x, y⁆ := by
  have hy : y = ∑ c : Coord n, y c.1 c.2.1 c.2.2 • unit K n c.1 c.2.1 c.2.2 := by
    conv_lhs => rw [← (glBasis K n).sum_repr y]
    simp only [glBasis_repr, glBasis_apply]
  rw [glSymbol_ξ_apply, map_sum]
  conv_rhs => rw [hy, lie_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Derivation.map_smul, coadDer_X, lie_smul, map_smul, glSymbol_ξ_apply]

omit [CharZero K] in
/-- `coadDer` as a Leibniz endomorphism, as used by `SymbolData.symbol_commutator`. -/
theorem coadDer_isLeibniz (x : GLProd K n) :
    IsLeibniz ((coadDer K n x).toLinearMap) := by
  intro f g
  change coadDer K n x (f * g) = f * coadDer K n x g + coadDer K n x f * g
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/-- The orbit statement for `K = ℂ` (see the module docstring). -/
def OrbitVanishingStatement : Prop :=
  ∀ (W : Submodule ℂ (MvPolynomial (Coord n) ℂ)),
    (∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W) →
    ∀ (c : ∀ i, Fin (n i) → ℂ), (∀ (i : ι) (p : Fin (n i)), (p : ℕ) + 1 < n i → c i p ≠ 0) →
    (∀ f ∈ W, eval (fun v : Coord n => if (v.2.2 : ℕ) = v.2.1 + 1 then c v.1 v.2.1 else 0) f = 0) →
    ∀ f ∈ W, ∀ M : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ, (∀ i, IsNilpotent (M i)) →
      eval (fun v : Coord n => M v.1 v.2.1 v.2.2) f = 0

end Langlands.Archimedean.Kostant
