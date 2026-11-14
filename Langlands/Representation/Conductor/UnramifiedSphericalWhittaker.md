# Spherical Whittaker functions of unramified principal series over every local field

Module `Langlands.Representation.Conductor.UnramifiedSphericalWhittaker`.

This module proves Shintani's characterization of the class-one Whittaker function by
its Hecke eigen-equations, and applies it to the unramified principal series `I(z)` of
`GL_(n+1)(F)`. For every inverse-character functional `ℓ` on `I(z)`, the coefficient
function `g ↦ ℓ(I(z)(g) f₀)` of the normalized spherical section `f₀` equals
`ℓ(f₀) · W(g; z; ψ̄)`. Here `W(·; z; ψ̄)` is the Library's explicit function
`inverseSphericalWhittaker hψ.1 hϖ q z`. The result holds for every Satake parameter
`z : Fin (n + 1) → ℂˣ` (not only unitary ones) and over every nonarchimedean local field
(`IsNonarchimedeanLocalField F`), including positive characteristic. The function-level
and representation-level uniqueness theorems hold over every field with a valuation, a
uniformizing element and a finite set of residue lifts. Nothing here uses `PadicField`.

The module does not prove `ℓ(f₀) ≠ 0` for some `ℓ`. That is Lemma 2 of Jacquet 2012,
the Library statement `OrderedUnramifiedWhittakerRealizationStatement`.

It also proves the module-level fact needed by the corank-one functional equation: the
central element `-1` acts trivially on `I(z)`, so every Whittaker model of `I(z)` has
minus-one scalar `1` (`hasModelMinusOneScalar_principalSeries`).

## Provenance

Shintani 1976 (literature ID `shintani-1976-class-one-whittaker`, p. 180) characterizes
the class-one Whittaker function `W_λ` on `GL_n` over a p-adic field by three properties:
`N`-equivariance, the Hecke eigen-equation, and `W(1) = 1`. The function is determined by
its values `w(f) = W(ϖ^f)`, which vanish unless `f` is antitone. The Library's
`Langlands/Representation/Whittaker/Spherical.md` records that the identification of
`sphericalWhittaker` with the Whittaker function of the normalized spherical vector was
left open there. This module supplies that identification for the coefficients of the
normalized spherical section of `I(z)`. Jacquet, Piatetski-Shapiro and Shalika 1981
(literature ID `jpss-1981-conductor`), Section (4.2), use this identification for the
spherical function `W(g; x; ψ̄)` of the unramified principal series.

The proof route is internal to this project. It uses only the standard minuscule coset
sums `K t_k K = ⊔ α t_α K` with their labelled representatives (the Library's
`labelledRep`) and the central element `ϖ⁻¹ = ϖ^(-1, …, -1)`, not the full Hecke
algebra. The vanishing argument is the Library's `eq_zero_of_satisfiesHeckeRecursion`
(module `Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness`), a
statement about functions on `ℤ^(n+1)` with no field. The minuscule eigenvalues of the
explicit function are the Library's field-generic `sphericalWhittakerMinusculeSum_eq`.

## Results

Throughout the first two sections, `F` is a field with a valuation `v`, `ϖ` is a
uniformizing element (`IsUniformizingElement v ϖ`), `θ` is a character of the upper
unipotent group `U` that is trivial on `U(O)` (`IsIntegrallyTrivial v θ`) and nontrivial
on each simple root group at level `ϖ⁻¹` (`hθ`), and `σ : Λ → F` is a set of `q`
residue lifts (`hσ`, `hinj`, `hsurj`, `Fintype.card Λ = q`, `0 < q`).

### Functions (namespace `Langlands.Conductor`)

- `eq_zero_of_minusculeRelations`. Let `f : GL_(n+1)(F) → ℂ` be `θ`-equivariant on the
  left (`f(u g) = θ(u) f(g)`) and right `GL_(n+1)(O)`-invariant. Suppose that for every
  `1 ≤ k ≤ n + 1` some scalar `c_k` satisfies `∑_α f(g t_α) = c_k f(g)` for all `g`,
  that some scalar `c` satisfies `f(g ϖ⁻¹) = c f(g)` for all `g`, and that `f(1) = 0`.
  Then `f = 0`. Proof: let `d(λ) = f(ϖ^λ)`. It vanishes off antitone `λ`
  (`eval_torus_eq_zero_of_not_antitone`). By `sum_eval_torus_mul_labelledRep`, the
  minuscule relations at `ϖ^λ` give the recursion `SatisfiesHeckeRecursion` with
  weights `q^(#radical pairs)`, which are nonzero. So `d` vanishes on every partition
  exponent (`eq_zero_of_satisfiesHeckeRecursion`). Shifting by the central relation
  `d(λ - (j, …, j)) = c^j d(λ)` moves every antitone `λ` to a partition exponent, so `d`
  vanishes everywhere. The Iwasawa decomposition `g = u ϖ^λ k`
  (`exists_eq_unipotentPart`) gives `f(g) = θ(u) d(λ) = 0`.
- `sum_sphericalWhittaker_mul_labelledRep`. The explicit function
  `W = sphericalWhittaker hϖ θ q x` satisfies
  `∑_α W(g t_α) = q^(k(n+1-k)/2) e_k(x) W(g)`, where `e_k(x)` is the Library's
  `elementaryCoefficient (Eigenvalues.ofTuple x) k`. Proof: evaluate the Library's
  polynomial identity `sphericalWhittakerMinusculeSum_eq` at `x`
  (`symmetricTorusEvaluation`).
- `sphericalWhittaker_mul_torus_neg_one`. `W(g ϖ⁻¹) = (∏ x_i)⁻¹ W(g)`. Proof: evaluate
  the Library's `sphericalWhittakerPolynomial_mul_torus_const` at `x`. The determinant
  unit evaluates to `∏ x_i`.
- `eq_smul_sphericalWhittaker` (Shintani's uniqueness). If `f` is as in
  `eq_zero_of_minusculeRelations`, the minuscule sums act on `f` by
  `q^(k(n+1-k)/2) e_k(x)` and `ϖ⁻¹` acts by `(∏ x_i)⁻¹`, then
  `f = f(1) • sphericalWhittaker hϖ θ q x`. Proof: apply
  `eq_zero_of_minusculeRelations` to `f - f(1) W`, using the two previous results and
  `W(1) = 1` (`sphericalWhittaker_one`).

### Coefficients of a representation

- `coefficientMap_eq_smul_sphericalWhittaker`. Let `ρ` be a complex representation of
  `GL_(n+1)(F)`, `ℓ` a `θ`-functional on it, and `w` a vector fixed by `GL_(n+1)(O)` such
  that `∑_α ρ(t_α) w = q^(k(n+1-k)/2) e_k(x) • w` for `1 ≤ k ≤ n + 1` and
  `ρ(ϖ⁻¹) w = (∏ x_i)⁻¹ • w`. Then the coefficient function
  `(coefficientMap ρ ℓ w).val = (g ↦ ℓ(ρ(g) w))` equals
  `ℓ(w) • sphericalWhittaker hϖ θ q x`. Proof: the coefficient function satisfies the
  hypotheses of `eq_smul_sphericalWhittaker`, and its value at `1` is `ℓ(w)`.

### The unramified principal series

Here `F` is a nonarchimedean local field, `hϖ` a uniformizing element for its valuation,
`hq : IsResidueCardinality q`, and `z : Fin (n + 1) → ℂˣ`. `PrincipalSeries hϖ n hq z`,
`principalSeries hϖ n hq z`, `value`, `sphericalSection` and `normalizedCharacter` are
the Library's (module `Langlands.Representation.Conductor.UnramifiedPrincipalSeries`).

- `valueLinear`, `value_sum`, `value_smul`, `ext_value`: evaluation at a point is
  linear, and two sections with the same values are equal.
- `value_borel_mul`: `f(b g) = χ_z δ^(1/2)(b) f(g)` for `b` in the Borel subgroup.
- `eq_mul_sphericalSection_of_covariance`: a right `GL_(n+1)(O)`-invariant function
  with the same Borel covariance equals its value at `1` times `f₀`. Proof: write
  `g = b k` (`exists_borel_integral`) and use
  `sphericalSection_borel_mul_integral`.
- `sphericalSection_labelledRep`: `f₀(t_α) = δ^(1/2)(ϖ^(1_S)) ∏_(j ∈ S) z_j`, where `S`
  is the subset of the label `α`. Proof: `t_α` is a unipotent upper triangular matrix
  times `ϖ^(1_S)`.
- `sum_sphericalSection_labelledRep`: `∑_α f₀(t_α) = q^(k(n+1-k)/2) e_k(z)`. Proof: for
  each subset `S` of size `k` there are `q^(#radical pairs of S)` labels. The Library's
  field-free `radical_mul_halfModulus` turns `q^(#radical pairs) δ^(1/2)(ϖ^(1_S))` into
  `q^(k(n+1-k)/2)`, and `elementaryCoefficient_ofTuple` expands `e_k(z)` as a sum over
  `S`.
- `sum_principalSeries_labelledRep`: `∑_α I(z)(t_α) f₀ = q^(k(n+1-k)/2) e_k(z) • f₀`.
  Proof: the left side, as a function, is the Library's `minusculeSumOperator` applied
  to `f₀`. It has the Borel covariance of `I(z)` and is right `GL_(n+1)(O)`-invariant
  (`minusculeSumOperator_mul_integral`), so by `eq_mul_sphericalSection_of_covariance`
  it is its value at `1` times `f₀`. That value is `sum_sphericalSection_labelledRep`.
- `principalSeries_torus_neg_one`: `I(z)(ϖ⁻¹) f = (∏ z_i)⁻¹ • f` for every section `f`.
  Proof: `ϖ⁻¹` is central (`torus_const_commute`), so `f(g ϖ⁻¹) = f(ϖ⁻¹ g)`. It lies in
  the Borel subgroup with `δ^(1/2)(ϖ⁻¹) = 1` (`halfModulus_add_const`) and
  `χ_z(ϖ⁻¹) = ∏ z_i^(ord ϖ⁻¹) = (∏ z_i)⁻¹`.
- `principalSeries_neg_one`: `I(z)(-1) f = f`. Proof: `-1` lies in the Borel subgroup
  with diagonal entries of valuation `1`, so its normalized character value is `1`.
- `hasModelMinusOneScalar_principalSeries`: for every character `θ` of `U` and every
  `θ`-functional `ℓ` on `I(z)`,
  `Langlands.RankinSelberg.HasModelMinusOneScalar (principalSeries hϖ n hq z) ℓ 1`.
  Every element of the coefficient model is `g ↦ ℓ(I(z)(g) w)`, and
  `I(z)(-g) = I(z)(g) I(z)(-1)`.
- `coefficientMap_sphericalSection`. Let `ψ` have integer conductor
  (`HasIntegerConductor ψ`) and let `ℓ ∈ glInverseFunctionals ψ n (principalSeries hϖ n
  hq z)`. Then
  `(coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val =
  ℓ.val (sphericalSection hϖ n hq z) • (inverseSphericalWhittaker hψ.1 hϖ q z).val`.
  Proof: apply `coefficientMap_eq_smul_sphericalWhittaker` with `θ` the inverse standard
  character, `Λ` the residue field (finite of cardinality `q`), `σ` the Library's
  `residueClassLift`, the conductor witness `exists_adjacentUnit_ne_one`, the fixed vector
  `sphericalSection_fixed`, and the two previous principal-series results.
- `coefficientMap_sphericalSection_apply`: the same identity at each `g`.

## Dependencies

Imports, all from the current Library:
`Langlands.Representation.Conductor.SphericalHecke`,
`Langlands.Representation.Conductor.SphericalCentral`,
`Langlands.Representation.Conductor.UnramifiedPrincipalSeries`,
`Langlands.Representation.Conductor.EssentialExistenceReduction`,
`Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness`,
`Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells`,
`Langlands.Representation.RankinSelberg.SphericalTorusRecursion`,
`Langlands.Representation.Unramified.PrincipalSeriesHecke`,
`Langlands.Representation.RankinSelberg.FunctionalEquationStatement`.
