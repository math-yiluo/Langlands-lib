# Assembly of the factoriality criterion for split simply connected groups

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, verifies the hypotheses of the chart
criterion `uniqueFactorizationMonoid_of_chart`
(`Langlands.CommutativeAlgebra.ChartUniqueFactorization`) for the coordinate
ring `A = Γ(G.X.left, ⊤)` and its function field `K`.

## Helpers

- `eq_of_le_of_height_eq_one`: in a domain, a nonzero prime `p` contained in a
  prime `q` of height one equals `q`.
- `specializes_iff_primeIdealOf_le`: in an affine scheme, `x ⤳ z` iff the prime
  of `x` is contained in the prime of `z`.
- `subset_closure_of_height_eq_one`: let `X` be integral and affine, let `q` be a
  height-one prime of `Γ(X, ⊤)` with point `y`, and let `V ⊆ X` be nonempty.
  Let `T` be an irreducible closed set that contains `closure {y}` and is
  disjoint from `V`. Then `T ⊆ closure {y}`, so `T = closure {y}`. The lemma
  does not assume that `closure {y}` itself is disjoint from `V`. When it is,
  `closure {y}` is a maximal member of the family of irreducible closed sets
  disjoint from `V`; the assembly below checks this disjointness separately.

  Proof: the generic point `ξ` of `T` specializes to `y`, so its prime is
  contained in `q`. That prime is nonzero: otherwise `ξ` would specialize to a
  point `z ∈ V`, which would then lie in `T`, contradicting `T ∩ V = ∅`. Since
  `q` has height one, the prime of `ξ` equals `q`, so `ξ = y` and
  `T = closure {ξ} = closure {y}`.
- `isAffine_cellSpec` and `uniqueFactorizationMonoid_cellSpec`: the cell spectrum
  is affine, and its global sections are factorial.
- `charSection_mul_neg`: `charSection χ · charSection (-χ) = 1`.
- `prime_boundarySection`: the boundary function `1 + y_{-a}` is prime in the
  global sections of the cell spectrum.
- `toFunctionField_charSection_mem`: on every chart, a torus character and its
  inverse lie in the chart subalgebra.
- `basicOpen_boundary_subset`: the part of the translated chart `tchart a` where
  `1 + y_{-a}` is invertible lies in the big cell. Its points come from the
  boundary localization, and `exists_boundary_comparison` maps them into `Ω`.

## The main result

`uniqueFactorizationMonoid_of_weights`: let `G.X.left` be integral, affine,
smooth over `k` and connected, with `A` Noetherian and integrally closed. Given
`D : CellData k G`, enumerations `neg` and `pos`, and fundamental weights `ω`
(`⟨ω i, j∨⟩ = δᵢⱼ` on simple roots), `A` is a unique factorization monoid.

The data for the criterion:

- the chart `S = sectionSubalgebra (Ω)`, the image of the big cell. It is
  factorial (`chartEquiv`, module `FactorialCellRing`) and a chart
  (`isChart_sectionSubalgebra`);
- the index set: the simple roots `a`;
- `f a`, the character `ω_a` read on the big-cell chart. It and its inverse lie
  in `S`;
- `p a`, the contraction to `A` of the prime `(π_a)` of the translated chart
  `S_a = sectionSubalgebra (u_a(1) · Ω)`, where `π_a` is the boundary function
  `1 + y_{-a}`.

The hypotheses are checked as follows.

- By `toFunctionField_charSection` (module `FactorialBoundaryChart`) and
  `⟨ω_a, b∨⟩ = δ_{ab}`, we have `f a = U_{a a} · π_a` and `f a = U_{a b}` for
  `a ≠ b`. Here `U_{a b}` is `ω_a` read on `S_b`, a unit of `S_b`.
- Since `S_a` is a chart, localizing `A` at `p a` agrees with localizing `S_a` at
  `(π_a)`. This gives:
  - `f a` is regular at `p a`;
  - `(f a)⁻¹` is not regular at `p a` (`inv_notMem_chartLoc`);
  - every nonzero `x` is `(f a)ⁿ` times a unit at `p a`
    (`exists_zpow_mul_unit` in the factorial ring `S_a`);
  - `f b` is a unit at `p a` for `b ≠ a`.
- Exhaustion: let `q` be a height-one prime of `A` with point `y`.
  - If `y ∈ Ω`, then `q` comes from a prime of `S` (`exists_prime_comap_eq`).
  - If `y ∈ u_a(1) · Ω`, then `y` is not in the basic open of `π_a`
    (`basicOpen_boundary_subset`), so `π_a` lies in the prime `Q'` of `y` in
    `S_a`. Now `Q'` has height one (`height_comap_eq`), so `(π_a) = Q'` and
    `q = p a`.
  - Otherwise `closure {y}` is disjoint from `Ω` and, separately, from every
    translated chart: a point of `closure {y}` in one of these open sets would
    put `y` in it. Every irreducible closed set containing `closure {y}` and
    disjoint from `Ω` is contained in `closure {y}`
    (`subset_closure_of_height_eq_one` with `V = Ω`, which is nonempty because
    the cell source is). Together with the disjointness of `closure {y}` from
    `Ω` just shown, this makes `closure {y}` a maximal irreducible closed set
    disjoint from `Ω`. This maximality is relative to `Ω` alone. These are the
    hypotheses of `false_of_maximal` (module `FactorialExhaustion`), which
    gives a contradiction.

Provenance: internal. This follows steps 2 to 6 of the Popov-style route
suggested in the task context, with the boundary charts given by root-group
translates `u_a(1) · Ω` instead of Weyl translates.
