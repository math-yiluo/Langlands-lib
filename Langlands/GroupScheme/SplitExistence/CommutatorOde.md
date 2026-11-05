# The commutator of two root exponentials over a polynomial ring

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.CommutatorOde`.

## Declarations

- `commRoots P γ δ`: the set of roots `θ` with `root θ = a • root γ + c • root δ` for some
  natural numbers `a, c ≥ 1`. Lemmas: `commRoots_pos` (`h` is positive on it when `h` is
  positive on `γ` and `δ`); `commRoots_closed` (closed under `(a, b) ↦ a + m • b`, `m ≥ 1`);
  `commRoots_add` (closed under adding positive multiples of `root γ`); and `subset_commRoots`
  (it contains the roots `root δ + m • root γ`, `m ≥ 1`).
- `commutator_ode_aux`: a noncommutative ring identity that gives the derivative of the
  commutator.
- `LieRootData.exists_list_commutator_poly` (`J` finite; `A` a torsion-free commutative
  `ℚ`-algebra; `t ∈ A`; `h : X →+ ℤ` positive on the roots `γ` and `δ`): over `A[X]`,
  `x_γ(X) x_δ(t) x_γ(-X) x_δ(-t) = ∏_{(θ, f) ∈ L} x_θ(f)` for some list `L`. Its roots lie in
  `commRoots P γ δ`, are pairwise distinct, and have nondecreasing `h`-values.

Proof: write `c = x_γ(X) x_δ(t) x_γ(-X) x_δ(-t)`. Using `mderiv_divExp`, the fact that `E_γ`
commutes with `x_γ`, and `commutator_ode_aux`, one gets `c' = M c` with
`M = -x_γ(X) (x_δ(t) E_γ x_δ(-t) - E_γ) x_γ(-X)`. By `conj_sub_mem` (with the roles of the two
roots exchanged), `x_δ(t) E_γ x_δ(-t) - E_γ` lies in the span of the `E_θ` with
`root θ = root γ + m • root δ`, `m ≥ 1`, which lies in the span over `commRoots`. By `conj_mem`,
conjugation by `x_γ(X)` keeps it there. Also `c(0) = x_δ(t) x_δ(-t) = 1`. Now apply `ode_peel`
to the finite set `commRoots P γ δ`.

Provenance: internal proof route for Chevalley's commutator formula (Steinberg, *Lectures on
Chevalley groups*, §3), over polynomial rings in characteristic zero.
