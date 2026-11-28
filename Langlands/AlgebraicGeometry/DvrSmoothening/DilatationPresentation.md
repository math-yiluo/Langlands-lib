# The defect drop for a dilatation, in terms of presentations

## Differentials at a point

For an algebra map `P → S` of `R`-algebras and an `S`-algebra `L`:

- `tensorKaehlerMap R L : L ⊗_P Ω_{P/R} → L ⊗_S Ω_{S/R}`, with `tensorKaehlerMap_tmul` and
  `tensorKaehlerMap_tmul_D`.
- `tensorKaehlerMap_surjective`, `ker_tensorKaehlerMap`: for surjective `P → S` the map is
  surjective with kernel spanned by the `1 ⊗ dg`, `g ∈ ker(P → S)` (conormal sequence
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, tensored with `L`).
- `one_tmul_D_mul`, `one_tmul_D_mul_of_eq_zero`, `one_tmul_smul`, `one_tmul_D_smul`: the Leibniz
  rule at the point, `1 ⊗ d(pq) = p(L) · (1 ⊗ dq) + q(L) · (1 ⊗ dp)`.

## The comparison theorem

`torsionLength_lt_of_dilatationPresentation`: let `P → A` and `P₂ → A₂` be surjections of
`R`-algebras with a compatible map `P → P₂`, and `R'` a discrete valuation ring which is an algebra
over all of them compatibly, in which `ϖ ∈ R` is a uniformizer. Suppose:

- `Ω_{P/R}` has a basis indexed by a finite type `σ` and `Ω_{P₂/R}` a basis indexed by
  `σ ⊕ Fin n`, the `inl` part being the image of the first and the `inr j` vector being `d Xⱼ`
  for elements `Xⱼ ∈ P₂` (finite rank is essential: for infinite rank the torsion lengths of
  `R' ⊗_A Ω_{A/R}` and `R' ⊗_{A₂} Ω_{A₂/R}` can both be infinite);
- `zⱼ, wₗ ∈ P`, the `wₗ` relations of `A`, with `zⱼ − ϖ Xⱼ` relations of `A₂`;
- `A₂` has no `ϖ`-torsion, and relations of `A` map to `0` in `A₂`;
- every relation `f` of `A` has a multiple `e f`, with `e` of unit value in `R'`, in
  `(ϖ, z)² + (w)`;
- every element `g ∈ P₂` satisfies `ϖ^v (e g) ∈ P + (zⱼ − ϖ Xⱼ)` for some `e` of unit value;
- elements of `P` mapping to `0` in `A₂` are, up to such a multiplier, `ϖ`-power torsion in `A`;
- the `1 ⊗ dzⱼ, 1 ⊗ dwₗ` are linearly independent over the residue field of `R'`.

If `R' ⊗_A Ω_{A/R}` has non-zero torsion, the torsion of `R' ⊗_{A₂} Ω_{A₂/R}` is strictly shorter.
The proof writes both modules as quotients `F_P ⧸ N_P` and `F₂ ⧸ N₂` of the free modules
`F_P = R' ⊗_P Ω_{P/R}` and `F₂ = R' ⊗_{P₂} Ω_{P₂/R}` by the evaluated differentials `d` of the
relations, and verifies the hypotheses of `DilatationLattice.torsionLength_lt_of_presentations`
for the map `θ₀` (basis vector `inl i` to `ϖ²` times the `i`-th basis vector, `inr j` to
`ϖ dzⱼ`) and the map `α : F_P → F₂` induced by `P → P₂`. Both directions are congruences of
evaluated differentials, not equalities of relations:

- *Forward.* For a relation `f` of `A`, write `e f = ϖ² r₀ + ϖ ∑ zⱼ gⱼ + ∑ zᵢ zⱼ gᵢⱼ + ∑ cₗ wₗ`
  with `e` of unit value. In `P₂` this reads `e f = ϖ² r + ∑ cₗ wₗ` modulo the ideal of the
  `zⱼ − ϖ Xⱼ`, with `r = r₀ + ∑ Xⱼ gⱼ + ∑ Xᵢ Xⱼ gᵢⱼ`. (The Lean proof obtains this from the
  inclusion of `(ϖ, z)² + (w)` in the inverse image of `(ϖ²) + (w) + (zⱼ − ϖ Xⱼ)` under `P → P₂`,
  checked on products of generators.) Since `A₂` has no `ϖ`-torsion, `r` is a
  relation of `A₂` (the divided relation). Applying `θ₀`, which kills the `d(zⱼ − ϖ Xⱼ)` and
  multiplies `α` by `ϖ²`, and cancelling `ϖ²` in the free module `F_P` gives
  `d(e f) = θ₀(d r) + ∑ χ₂(cₗ) dwₗ`; so `d f` is `θ₀` of an element of `N₂` modulo the span of
  the `dwₗ` (`χ₂` is evaluation at the point).
- *Reverse.* For a relation `g` of `A₂`, the hypothesis on `P₂` gives `ϖ^v (e g) = c + κ` with `c`
  from `P`, `e` of unit value and `κ` in the ideal of the `zⱼ − ϖ Xⱼ`; then `c` maps to `0` in
  `A₂`, and by the kernel hypothesis `ϖ^{v'} e' c` is a relation of `A` for some `e'` of unit value.
  Clearing these powers of `ϖ` and unit values, the evaluated differential `ϖ^{v+v'} d g` equals
  `α(d(ϖ^{v'} e' c))`, rescaled by a unit, modulo the span of the `α dwₗ` and the
  `α dzⱼ − ϖ dXⱼ` (the auxiliary differentials). This passes from the generators `d g` to all of
  `N₂` by induction over the span, adding the exponents of `ϖ` for sums.
- In the forward direction the statement for the generators `d f` likewise gives it for all of
  `N_P`, since the elements `θ₀ y + (span of the dwₗ)`, `y ∈ N₂`, form a submodule.

This is the computation of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3, proof of
Proposition 5 (printed pp. 69–71), with the smooth ambient scheme replaced by polynomial
presentations and Jacobian minors replaced by the lattice comparison.
