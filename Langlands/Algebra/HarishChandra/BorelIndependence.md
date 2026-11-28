# Independence of the Borel subalgebra for the shifted central characters

Module `Langlands.Algebra.HarishChandra.BorelIndependence`, namespace
`Langlands.Algebra.HarishChandra`.

## Definitions

- `WeightBasis H`: a basis `b` of simultaneous eigenvectors of `ad 𝔥` with weights given as
  linear forms `w a`, containing at most one vector of each nonzero weight.
  `IsSplitCartan.nonempty_weightBasis` constructs one. Every root is some `w a`
  (`exists_index`), and so is the negative of every root (`exists_neg`).
- `WeightBasis.rho X = ½ Σ_{a : Re w a(X) > 0} w a`, half the sum of the roots positive at `X`.
- `WeightBasis.det a a' X X'`: the determinant of the real parts of `w a`, `w a'` at `X` and
  `X'`. If both roots vanish at a point of the segment from `X` to `X'`, it vanishes.
- `WeightBasis.IsGeneric X X'`: this determinant is nonzero for every pair of roots from
  distinct pairs of opposite roots.
- `WeightBasis.crossings X X'`: the roots positive at `X` and negative at `X'`.

## Results

- `positiveRootSubmodule_eq_of_iff`, `rho_eq_of_iff`, `vermaIdeal_eq_of_iff`: elements with the
  same positive roots have the same mirror Verma ideals and the same `ρ`.
- `rho_sub_rho_of_wallCrossing`: across a wall, `ρ_X - ρ_{X'} = α`.
  `sub_mem_vermaIdeal_rho_of_wallCrossing` combines this with `WallCrossing.sub_mem_vermaIdeal`.
- `exists_forall_ne_zero_of_real_linear`: finitely many nonzero real-linear functionals on a
  complex vector space have a common point where none vanishes (induction on the finite set).
- `exists_step`: on a generic segment with a crossing, let `t₀` be the first crossing time,
  attained by the root `α`. Take a point `X''` of the segment after `t₀` and before every later
  crossing time. Genericity makes `±α` the only roots crossing at `t₀`. So `X` and `X''` form a
  wall crossing along `α`, `X''` is real-regular, the segment from `X''` to `X'` is generic, and
  it has one crossing fewer.
- `sub_mem_of_isGeneric`: by induction on the number of crossings, along a generic segment
  `z ≡ s` modulo `R_X(λ + ρ_X)` implies `z ≡ s` modulo `R_{X'}(λ + ρ_{X'})`.
  With no crossings the positive roots agree (`iff_of_crossings_eq_empty`).
- `exists_generic`: the endpoint `X'` can be replaced by `X' + δZ` with the same positive roots
  and a generic segment from `X`. Choose `Z` with `det a a' X Z ≠ 0` for all relevant pairs.
  These functionals are nonzero because a root whose real part is a real multiple of another's
  is that multiple of it, and the root system is reduced. Then choose a small `δ > 0` avoiding
  finitely many values.
- `sub_mem_vermaIdeal_rho`: **independence of the Borel subalgebra.** For central `z` and
  real-regular `X, X'`, `z ≡ s` modulo `R_X(λ + ρ_X)` implies `z ≡ s` modulo
  `R_{X'}(λ + ρ_{X'})`.

This is the independence of the `ρ`-shifted Harish-Chandra homomorphism from the Borel subalgebra
containing the Cartan subalgebra: the case of Borel subalgebras of Knapp–Vogan, *Cohomological
Induction and Unitary Representations* (1995), Chapter IV §8, Proposition 4.129(c), in
right-ideal form. The proof compares adjacent Borel subalgebras through mirror Verma modules.
