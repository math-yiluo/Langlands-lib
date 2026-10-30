# The unipotent transform of a matrix Schwartz–Bruhat function

Module `Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`, namespace
`Langlands.RankinSelberg.RankOneIwasawa`. This is a helper module of the positive-rank
branch of the proof of `RankOneMatrixWhittakerComparisonStatement`. Throughout, `F` is a
`p`-adic field with its canonical topology, valuation and local-field structure, and
`𝓛 a = F.canonicalTopologicalData.additiveLattice a` is the published lattice `π^(-a) O`.

## Lattice arithmetic and uniform constants

- `lattice_mul`, `lattice_mono`, `inv_mem_lattice_of_notMem`, `exists_mem_lattice`,
  `mem_lattice_zero_iff` (`𝓛 0` is the valuation integer ring), `isOpen_lattice` and
  `isCompact_lattice` (from the published `padicLatticeGeometry`).
- `matLattice F r a` is the additive subgroup of `r × r` matrices with all entries in
  `𝓛 a`. Products add levels (`matLattice_mul`). Integral matrices are level `0`
  (`integralSubgroup_mem_matLattice`). These subgroups are open (`isOpen_matLattice`),
  exhaust all matrices (`exists_mem_matLattice`) and form a neighbourhood basis of zero
  (`matLattice_basis`, proved with `isOpen_pi_iff'` on both matrix indices).
- `exists_filtration_bounds` is a general lemma. A locally constant, compactly supported
  function on a topological additive group with such a filtration is supported in one
  member and invariant under another. The proof adapts the published proof of
  `padicSchwartzBruhat_exists_additiveLattice_invariant` (compact cover, finite subcover,
  minimum level). It gives `schwartz_support_bound` and `schwartz_invariance` for matrix
  test functions.
- `schwartzOfLattice` packages a function on `F` that is invariant under one lattice and
  supported in another as a Schwartz–Bruhat function.

## The transform

`unipotentTransform F ψ Φ M = ∫_N Φ(u M) θ(u) du` uses `unipotentHaar` and the standard
character `θ = standardCharacter ψ n`. It is defined for every matrix `M`, including
singular ones, as a Bochner integral.

- `unipotentTransform_unipotent_mul`: `J(ν M) = θ(ν)⁻¹ J(M)`, by right invariance of
  `unipotentHaar` (`unipotentHaar_isMulRightInvariant`).
- `unipotentTransform_mul_right`: every right invariance `Φ(X κ) = Φ(X)` passes to `J`.
- `unipotentTransform_eq_zero_of_shift`: suppose right translation of the integration
  variable by `elemUnipotent i t = 1 + t E_{i,i+1}`, with `ψ(t) ≠ 1`, leaves the integrand
  unchanged. Then `J(M) = ψ(t) J(M)`, so `J(M) = 0`. The value
  `θ(1 + t E_{i,i+1}) = ψ(t)` is `standardCharacter_elemUnipotent`.
- `exists_lattice_nontrivial`: since `ψ` is nontrivial, it is nontrivial on some lattice.
  This uses the published `additiveTrivialAt_bddAbove`.

## Support of the transform on `diag(d) k`

`unipotentTransform_diag_bounds` gives levels `R` and `E` with the following property.
Let `d` be a unit diagonal and `k` integral, and suppose `J(diag(d) k) ≠ 0`. Then every
`dᵢ` lies in `𝓛 R`, and `dᵢ⁻¹` lies in `𝓛 E` for every `i ≥ 1`. The upper bound
follows from the support of `Φ`: the diagonal entries of `u · diag(d)` are the `dᵢ`. The
lower bounds are proved by induction on the column:

- `ColBound F Φ M j B` says that column `j` of every `u` with `Φ(u M) ≠ 0` has entries in
  `𝓛 B`. Column `0` is the first unit vector (`colBound_zero`). A lower bound for `dⱼ`
  gives a bound for column `j` (`colBound_of_inv`), because `u_{aj} dⱼ` lies in the
  support lattice.
- `inv_mem_of_colBound`: if column `i` is bounded and `d_{i+1}` is too small, then
  right translation by `1 + t E_{i,i+1}`, with `t` in the nontrivial lattice of `ψ`,
  perturbs `u · diag(d) · k` by a matrix in the invariance lattice of `Φ`. This holds both
  for `u` and for `u (1 + t E_{i,i+1})`, which have the same column `i`. Hence `J`
  vanishes. Contrapositively, `d_{i+1}⁻¹` is bounded.

This is the support property of `Φ^θ(a k)` in Jacquet–Piatetski-Shapiro–Shalika (1979),
Section 4. It is proved here directly by translation; the route is internal.

`exists_cornerSchwartz`: for fixed `a` and integral `k`, the function
`x ↦ J(diag(x, a) k)` on all of `F` is Schwartz–Bruhat. It is invariant under the
invariance lattice of `Φ`, because `u E₀₀ = E₀₀` for unipotent `u`
(`unipotent_mul_single_zero`). It is supported in `𝓛 R`.

## Congruence subgroups

`congruenceGroup F n m` is the group of `k` such that `k - 1` and `k⁻¹ - 1` lie in
`matLattice (-m)`. It lies in `GL_(n+1)(O)` (`congruenceGroup_le_integral`), is normalized
by it (`conj_mem_congruenceGroup`), and is open (`isOpen_congruenceGroup`). Every open
subgroup contains one (`exists_congruenceGroup_le`); the proof uses the inducing map
`Units.embedProduct` and `matLattice_basis`. A matrix test function is right-invariant
under all deep enough congruence subgroups (`exists_schwartz_congruence`).

## Scope

All statements are proved. There are no hypotheses on convergence, admissibility or
finite generation. The module concerns only the test function, the character and the
unipotent integral.
