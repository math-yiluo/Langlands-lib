# Admissibility of irreducible quasicuspidal product-Levi representations

Authors: Worker 237.

`Langlands.CuspidalSupport.LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility`
proves the published proposition family
`Langlands.CuspidalSupport.IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF,uV} F T B`
of `Langlands/Representation/CuspidalSupport/QuasicuspidalPrerequisitesStatement.lean`
for every prime `p`, every `F : PadicField.{uF} p`, every compatible topological
datum `T`, every rank `n` and every block shape `B : BlockShape n`, including the
empty shape and rank zero. The field universe `uF` and the carrier universe `uV`
stay independent. No hypothesis is added to the target. In particular, finite
length, a central character and countability of the carrier are not assumed; the
proof derives countable dimension and the scalar action of the block scalars.

The proof uses two published theorems:

- `Langlands.GeneralLinear.Cartan.cartanDecomposition` (module
  `Langlands.Group.GL.CartanProof`), the proof of
  `Langlands.GeneralLinear.CartanDecompositionStatement`. It is used at universes
  `.{uF, uF}`, with the valuation `ValuativeRel.valuation K` and its value group
  `ValuativeRel.ValueGroupWithZero K`, where `K` is the local field of section
  `Levi` below.
- `Langlands.countableDimensionalSchur` (module
  `Langlands.Representation.Schur.CountableDimensionProof`), the proof of
  `Langlands.CountableDimensionalSchurStatement`.

## Relation to the literature

Bernstein and Zelevinsky 1976 (literature id
`bernstein-zelevinsky-1976-representations-gln`), Theorem 3.25, prove
admissibility of irreducible representations of `G_α` through Harish-Chandra's
Theorem 3.21 (the restriction to `G_α⁰` is a finite representation, that is,
has compactly supported matrix coefficients), Lemma 3.26 (that restriction is a
direct sum of finitely many irreducible representations) and §2.41 (every
finitely generated finite representation, in particular every irreducible finite
representation, is admissible). Finite generation cannot be dropped in §2.41: an
infinite direct sum of trivial representations of a compact group is finite in
the sense of §2.40 but not admissible. In the source, Lemma 3.26 supplies it,
since a direct sum of finitely many irreducibles is finitely generated.
This module does not follow that route. It uses a direct argument that needs
only the Cartan decomposition and Schur's lemma in countable dimension
(BZ76 Proposition 2.11):

1. For an open subgroup `H`, every `H`-fixed vector is the average, over a
   compact open subgroup `K_c ⊆ H`, of a combination of translates `ρ(g) v₀` of
   one nonzero vector.
2. By the Cartan decomposition, `g = k₁ · t · k₂` with integral `k₁, k₂` and a
   block-diagonal torus element `t = diag(ϖ^λ)` with antitone exponents in each
   block.
3. If some gap `λ_i(a) - λ_i(a+1)` is large, the average vanishes: this is where
   quasicuspidality enters, through the Jacquet module of the parabolic that
   splits block `i` after position `a`. (This is the mechanism behind the
   compact support of matrix coefficients in BZ76 3.21, used here only in the
   form needed.)
4. If all gaps are bounded, `λ` differs from one of finitely many exponent
   tuples by a constant in each block, and block scalars act by scalars
   (Schur's lemma; countable dimension follows from the Cartan decomposition).

So every `H`-fixed vector lies in the span of finitely many vectors.

## Implemented proof

### Generic lemmas (section `Generic`)

For any group `G` and complex representation `ρ` on `V`:

- `exists_ne_zero_of_isIrreducible`: an irreducible representation has a
  nonzero vector, since `⊥ ≠ ⊤` among its subrepresentations.
- `span_orbit_eq_top`: the span of the orbit of a nonzero vector `v` is a
  subrepresentation containing `v`, so it is everything by irreducibility.
- `exists_finset_mul_inv_mem`: a compact set `S` of a topological group is
  covered by finitely many right cosets `H c` of an open subgroup `H`
  (compactness applied to the open cover by the sets `H c`).
- `rank_le_aleph0_of_doubleCoset_cover`: if `ρ` is smooth and irreducible, `K` is
  a compact open subgroup and `G` is covered by double cosets `K s K` with `s` in
  a countable set `S`, then `Module.rank ℂ V ≤ ℵ₀`. The `K`-orbit of every vector
  is finite (`Compact.finite_orbit_of_smooth`), so the orbit of a nonzero `v₀`
  lies in the countable union over `s ∈ S` and `w` in the `K`-orbit of `v₀` of
  the `K`-orbits of `ρ(s) w`. That orbit spans `V`, and `rank_span_le` bounds the
  rank by its cardinality. This is how countable dimension is derived without
  any countability hypothesis on the carrier.
- `exists_scalar_of_central`: if `z` is central, `ρ(z)` is an intertwiner of `ρ`
  with itself, so the published countable-dimension Schur theorem
  `Langlands.countableDimensionalSchur` makes it a scalar.

### The product Levi (section `Levi`)

Here `K` is a nonarchimedean local field (`IsNonarchimedeanLocalField`) and `B`
a block shape.

The compact open subgroup `integralLevi B` (the product of the integral
subgroups of the blocks) and its compactness, the deep-vanishing lemmas
`exists_gap_average_eq_zero` and `exists_uniform_gap_bound`, and the finite set of
bounded-gap representatives `boundedGapReps` are in the auxiliary module
`LeviGapVanishing`, whose Markdown describes their proofs. In brief: if some gap
`λ_i(a) - λ_i(a+1)` of a blockwise antitone exponent tuple `λ` is large, the
average over a compact open subgroup of `ρ(c · leviTorus B ϖ λ) w` is zero,
because quasicuspidality puts `w` in the Jacquet coinvariant kernel of the parabolic
that splits block `i` after position `a`, and conjugation by the torus contracts
that unipotent radical into the subgroup. If all gaps are below `N`, `λ` is one of
finitely many tuples plus a constant in each block.

- `exists_levi_cartan`: applying `Cartan.cartanDecomposition` in each block gives
  `g = k₁ · leviTorus B ϖ λ · k₂` with `k₁, k₂ ∈ integralLevi B` and every
  `λ j` antitone.
- `finite_fixedVectors` (assembly): let `K₀ = integralLevi B` and
  `K_c = H ⊓ K₀`, compact and open. Fix `v₀ ≠ 0`, its finite `K₀`-orbit `W` and a
  finite set `C` with `K₀ ⊆ ⋃_{c ∈ C} K_c c`. Take the uniform bound `N` for the
  pairs `(c, w) ∈ C × W` and the finite set `Λ₀` of bounded-gap
  representatives. Let `Φ` be the finite set of `K_c`-averages of
  `ρ(c · leviTorus B ϖ μ) w` with `c ∈ C`, `μ ∈ Λ₀`, `w ∈ W`. For any `g`,
  write `g = k₁ t k₂` (Cartan) and `k₁ = h c` with `h ∈ K_c`; then the average of
  `ρ(g) v₀` is the average of `ρ(c t)(ρ(k₂) v₀)`. If some gap of `t` is at least
  `N` this is zero; otherwise `t = leviTorus B ϖ μ · z` with `μ ∈ Λ₀` and a block
  scalar `z` (`leviTorus_add_const`), which commutes with everything and acts by
  a scalar (hypothesis `hscalar`), so the average lies in `span Φ`. The orbit of
  `v₀` spans `V`, so averaging maps all of `V` into `span Φ`. An `H`-fixed vector
  is `K_c`-fixed and equals its own average (`Compact.averageMap_id`), so the
  `H`-fixed vectors lie in the finite-dimensional `span Φ`.
- `isAdmissible_of_isLeviQuasicuspidal`: choose a uniformizer
  (`Iwasawa.exists_isUniformizingElement`). Countable dimension follows from
  `rank_le_aleph0_of_doubleCoset_cover` with `K = integralLevi B` and the
  countable set of all `leviTorus B ϖ λ` (Cartan). Each block scalar
  `leviTorus B ϖ (fun j _ => c j)` is central (`leviTorus_const_comm`), hence acts
  by a scalar (`exists_scalar_of_central`). Smoothness is given, and
  `finite_fixedVectors` gives finite-dimensional fixed spaces for every open
  subgroup, which is `IsAdmissible`.

### The target

`irreducibleQuasicuspidalLeviAdmissibility` installs the topology, valuative
relation and local-field instance of `T` and applies
`isAdmissible_of_isLeviQuasicuspidal` to `σ.representation`, with the
smoothness `σ.isSmooth`. The empty shape needs no separate case: the argument
above is uniform in `B` (with no blocks there are no gaps, and the box of
representatives is a single point).

The auxiliary module `LeviSplitContraction` provides the split refinements,
the contraction lemma and the block torus elements used above, and
`LeviGapVanishing` provides the integral Levi subgroup, deep vanishing and the
bounded-gap box. Neither auxiliary module uses the Cartan decomposition or Schur's
lemma.
