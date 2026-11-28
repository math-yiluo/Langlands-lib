# Proof that a characteristic-zero local field has finitely many subextensions of bounded degree

`Langlands.LocalField.finiteSubextensionsBoundedDegree` proves exactly the
published proposition `Langlands.LocalField.FiniteSubextensionsBoundedDegreeStatement`,
imported from `Langlands.LocalField.FiniteSubextensionsBoundedDegreeStatement`.

```lean
theorem finiteSubextensionsBoundedDegree : FiniteSubextensionsBoundedDegreeStatement.{u}
```

For every characteristic-zero nonarchimedean local field `F : Type u` and every
`d : ℕ`, the set of intermediate fields `E` of `AlgebraicClosure F / F` with
`FiniteDimensional F E` and `Module.finrank F E ≤ d` is finite. The theorem
invokes `FiniteSubextensionsBoundedDegree.finite_boundedDegree`. The auxiliary
declarations below are in the namespace
`Langlands.LocalField.FiniteSubextensionsBoundedDegree`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

The statement page derives the proposition from Serre, *Local Fields*, using
the maximal unramified subextension, an Eisenstein presentation of the remaining
totally ramified extension, compactness of the Eisenstein coefficients and
Krasner's lemma. The Lean proof constructs the intermediate field and the
Eisenstein generator directly inside the fixed algebraic closure
`Ω = AlgebraicClosure F`.

- For `M = q ^ d! - 1`, where `q` is the residue cardinality of `F`, an `M`-th
  root of unity means a solution of `ζ ^ M = 1`. For each `E`, let `U = F(S)`,
  where `S` consists of all `M`-th roots of unity in `E`. Since each `S` is a
  subset of the same finite root set in `Ω`, there are finitely many choices
  of `U`.
- An approximation argument shows that `E` is generated over `U` by an element
  of minimal positive valuation. The discreteness of the norms in `E`
  supplies a uniform factor by which each strict improvement in distance
  shrinks the error. Closedness of the span of the chosen powers then forces
  every element of `E` into the span.
- For each `U` and degree `m`, the coefficient set is a compact subset of
  `Ω^m` whose coordinates lie in `U`. Krasner's lemma over `F` and a degree
  comparison give equality of actual subfields of `Ω`.

## Normed setting

The base field `F` carries the local instance
`Langlands.LocalGalois.localNormedField F`, a complete ultrametric nontrivially
normed field whose topology is, by definition, the given topology of `F`
(`localNormedField_topology` is `rfl`). Thus `F` is locally compact for this
norm. `Ω` carries `spectralNorm.nontriviallyNormedField F Ω` and
`spectralNorm.normedAlgebra F Ω`, so `‖x‖ = spectralNorm F Ω x`. Mathlib's
`IsKrasner.of_completeSpace` then gives `IsKrasner F Ω`. These instances are local
to the proof module.

## Discreteness of norms

- By `baseNorm_eq_zpow`, every nonzero `a : F` has `‖a‖ = ‖uniformizer F‖ ^ k`
  for some `k : ℤ`. The proof compares norms with the integer order
  `FML.ord F` through `LocalGalois.localNormedField_le` and the order of
  `Plancherel.fieldOrderUnits`. The same argument appears as a private lemma in
  `Langlands.LocalField.AlgebraicExtensionValuation`.
- The minimal polynomial of `x` over `F` with degree `deg` and constant
  coefficient `a₀` satisfies `‖x‖ ^ deg = ‖a₀‖` by `norm_pow_natDegree`, using
  `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`.
- For `D > 0`, `sig F D` is `‖uniformizer F‖ ^ (1 / D)`. By
  `norm_eq_sig_zpow`, if the degree of a nonzero `x` divides `D`, then `‖x‖`
  is an integer power of `sig F D` (take `m`-th roots in
  `‖x‖ ^ m = ‖uniformizer F‖ ^ k`).
- By `exists_valueGenerator`, a finite subextension `K` contains `ϖ` with
  `0 < ‖ϖ‖ < 1` such that every nonzero `x ∈ K` has `‖x‖ = ‖ϖ‖ ^ j` for some
  `j : ℤ`. With `D = (finrank F K)!`, every nonzero norm on `K` is an integer
  power of `sig F D`. The uniformizer of `F` gives the exponent `D`, so
  `Nat.find` finds the smallest positive exponent `g`, which is attained
  by `ϖ`. Dividing `x` by a power of `ϖ` shows by the division algorithm that
  every exponent is a multiple of `g`.

## The approximation lemma

For `mem_of_approx`, let `V` be a finite-dimensional `F`-subspace of `Ω`, `x : Ω` and
`0 < c < 1`. Assume that for `v, w ∈ V` with `x - v ≠ 0`,
`‖x - w‖ < ‖x - v‖` implies `‖x - w‖ ≤ c * ‖x - v‖`, and that every `v ∈ V` with
`x - v ≠ 0` admits `w ∈ V` with `‖x - w‖ < ‖x - v‖`. Then `x ∈ V`. Indeed `V` is
closed (`Submodule.closed_of_finiteDimensional`). If `x ∉ V` its distance `δ` to
`V` is positive, some `v ∈ V` has `‖x - v‖ < δ / c`, and an improvement `w` gives
`‖x - w‖ ≤ c * ‖x - v‖ < δ`, which is impossible.

## Roots of unity

Let `kF` be the residue field of `LocalGalois.baseIntegers F` (finite by
`LocalGalois.localResidue_finite`), `q` its cardinality, and
`M = rootOrder F d = q ^ d! - 1`. The `M`-th roots of unity in `Ω` are the
solutions of `ζ ^ M = 1`. The lemmas `mem_integers_iff` and
`mem_maximalIdeal_iff` characterize the valuation ring
`LocalGalois.extensionIntegers F Ω` and its maximal ideal by `‖x‖ ≤ 1` and
`‖x‖ < 1`, respectively.

- By `norm_rootOrder`, `‖(rootOrder F d : Ω)‖ = 1` because the image of
  `q ^ d! - 1` in the residue field is the image of `-1` from `kF`, where
  `(q : kF) = 0` (`FiniteField.cast_card_eq_zero`).
- By `norm_pow_rootOrder_sub_one_lt`, if `‖u‖ = 1` and the degree of `u` over `F` is
  at most `d`, then `‖u ^ rootOrder F d - 1‖ < 1`. The minimal polynomial of `u`
  has coefficients of norm at most one (`spectralValue_le_one_iff`), hence lifts
  to a monic polynomial over `baseIntegers F` of the same degree, as in
  `LocalGalois.spectral_integral`. Its reduction annihilates the residue `ū` of
  `u`, so `kF⟮ū⟯` is a finite field with `q ^ f` elements for some `f ≤ d`. Since
  `f` divides `d!`, `FiniteField.pow_card_pow` gives `ū ^ (q ^ d!) = ū`, so
  `u (u ^ (q ^ d! - 1) - 1)` lies in the maximal ideal.
- By `norm_sub_eq_one_of_pow_eq_one`, distinct `M`-th roots of unity `ζ` and
  `ζ'` satisfy `‖ζ - ζ'‖ = 1`. Both have norm one. If `‖ζ - ζ'‖ < 1`, then
  `η = ζ' / ζ ≠ 1` would satisfy
  `‖η ^ i - 1‖ < 1` for all `i`, and the vanishing geometric sum
  `∑_{i < M} η ^ i = 0` would give `‖(M : Ω)‖ < 1`, contradicting
  `norm_rootOrder`.
- By `exists_rootOfUnity_near`, if `‖u ^ M - 1‖ < 1`, some `M`-th root of unity
  `ζ` has `‖u - ζ‖ < 1`, because `u ^ M - 1` is the product of
  the `u - ζ` (`Splits.eval_eq_prod_roots_of_monic`).
- In characteristic zero, `rootOfUnity_mem_adjoin` places such a `ζ` in `F⟮u⟯`
  by Krasner's lemma (`IsKrasner.krasner`). The element `ζ` is separable, and
  every conjugate `ζ'` also satisfies `ζ' ^ M = 1`. Each distinct conjugate
  is therefore at distance one from `ζ`, which is more than `‖u - ζ‖`.

## Conjugates and coefficients

- The lemma `norm_eq_of_isConjRoot` gives equal norms for conjugate elements
  over `F` using `spectralNorm_eq_of_equiv`.
- For an intermediate field `K`, `norm_root_minpoly` gives norm `‖x‖` for
  every root in `Ω` of the minimal polynomial of `x` over `K`. Its constant
  coefficient has norm `‖x‖ ^ deg` by `norm_coeff_zero_minpoly`, using the
  product of the roots (`Splits.coeff_zero_eq_prod_roots_of_monic`).
- If `‖x‖ < 1`, then `norm_coeff_minpoly_lt_one` shows that the non-leading
  coefficients of the minimal polynomial of `x` over `K` have norm less than
  one. It uses `norm_coeff_prod_lt_one`, which proceeds by induction on a
  multiset of roots.

## Eisenstein polynomials

`IsEis F U r g` says that `g : Polynomial U` is monic, its non-leading
coefficients have norm at most `r`, and its constant coefficient has norm
exactly `r`. When the nonzero norms of `U` are the integer powers of `r` with
`0 < r < 1`, this is the Eisenstein condition for the valuation ring of `U`.

- For `0 < r < 1`, `norm_pow_of_isEis` shows that every root `β` of a polynomial `g`
  satisfying `IsEis F U r` of degree `m ≥ 1` has `‖β‖ ^ m = r`. If `‖β‖ ^ m > r`
  the leading term dominates the other terms of `g(β)`, and if `‖β‖ ^ m < r` the
  constant term dominates. Both contradict `g(β) = 0` by the ultrametric inequality
  for finite sums.
- If moreover every nonzero norm on `U` is an integer power of `r`,
  `natDegree_minpoly_of_isEis` shows that every root of `g` has degree `m`
  over `U`. The minimal polynomial `h` of `β` divides `g`, and its constant
  coefficient has norm `‖β‖ ^ deg h`, an integer power of `r`. Comparing with
  `‖β‖ ^ m = r` forces `m` to divide `deg h`.

## Finiteness over a fixed field and degree

For `a : Fin m → Ω`, `coeffPoly F a` is `X ^ m + ∑ i, C (a i) * X ^ i`. The set
`eisSet F U r m hm` consists of the coefficient vectors with all entries in `U`
of norm at most `r` and `‖a 0‖ = r`. For each such `a`,
`exists_lift_of_mem_eisSet` gives a degree-`m` polynomial over `U` satisfying
`IsEis F U r` whose image in `Ω[X]` is `coeffPoly F a`. When `0 < r < 1` and
every nonzero element of `U` has norm `r ^ j` for some `j : ℤ`, its constant
coefficient has the norm of a uniformizer and the lift is Eisenstein.

- The positive radius `krasnerRadius F a` is the minimum of `1` and of the conjugate radii
  `Langlands.Global.FieldRealization.conjugateRadius F β` of the roots `β` of
  `coeffPoly F a`.
- For `adjoin_eq_of_close`, assume `F` has characteristic zero, `m ≥ 1`,
  `0 < r < 1`, and every nonzero element of `U` has norm `r ^ j` for some
  `j : ℤ`. Let `a ∈ eisSet F U r m hm` and let `Q` be monic of degree `m`
  over `U`, with each lower coefficient differing from the corresponding
  entry of `a` by an element of norm less than `krasnerRadius F a ^ m`.
  For a root `y` of `Q` with `‖y‖ ≤ 1`, the ultrametric inequality gives
  `‖(coeffPoly F a)(y)‖ < krasnerRadius F a ^ m`. Factoring this evaluation
  over `Ω` gives a root `β` of `coeffPoly F a` with
  `‖y - β‖ < krasnerRadius F a`. Krasner's lemma over `F` gives `β ∈ F⟮y⟯`
  and hence `U⟮β⟯ ≤ U⟮y⟯`. The hypotheses on `r` ensure that `β` has degree
  `m` over `U` by `natDegree_minpoly_of_isEis`. Since the degree of `y` is at
  most `m`, the two fields are equal.
- When `U` is finite-dimensional over `F`, `isCompact_eisSet` proves that
  `eisSet F U r m hm` is compact. The closed ball of radius `r` in the
  finite-dimensional `F`-space `U` is compact (`FiniteDimensional.proper`).
  The product of `m` copies is compact, and `‖a 0‖ = r` is a closed condition.
- For `finite_eisensteinFields`, assume `F` has characteristic zero, `U` is
  finite-dimensional over `F`, and every nonzero norm on `U` is an integer
  power of `r` with `0 < r < 1`. For `m ≥ 1`, the set of fields
  `(U⟮ϖ⟯).restrictScalars F` with `‖ϖ‖ ≤ 1` and minimal polynomial over `U`
  of degree `m` satisfying `IsEis F U r` is finite. Cover `eisSet` by the
  balls of radius `krasnerRadius F a ^ m` and take a finite subcover
  (`IsCompact.elim_nhds_subcover`). By `adjoin_eq_of_close`, every such field
  is `U⟮β⟯` for a root `β` of `coeffPoly F a` with `a` in the finite subcover.

## Structure of a subextension

For `exists_eisenstein_generator`, assume `F` has characteristic zero and `E`
is finite-dimensional over `F` of degree at most `d`. Let `S` be a finite
subset of `E` containing every `M`-th root of unity lying in `E`, where
`M = rootOrder F d`. Put `U = F(S)` and suppose `πU ∈ U` has `0 < ‖πU‖ < 1` with
every nonzero norm on `U` an integer power of `‖πU‖`. Then there is `ϖ` with
`‖ϖ‖ ≤ 1` whose minimal polynomial over `U` satisfies `IsEis F U ‖πU‖` and has
degree between `1` and `d`, with `E = (U⟮ϖ⟯).restrictScalars F`.

The proof takes `ϖ` from `exists_valueGenerator F E`, so `‖πU‖ = ‖ϖ‖ ^ e` with
`e ≥ 1`, and lets `V` be the `U`-span of `1, ϖ, …, ϖ ^ (e - 1)`, a
finite-dimensional `F`-subspace contained in `E`. Every `x ∈ E` lies in `V` by
`mem_of_approx` with shrink factor `‖ϖ‖`. Positive distances from `x` to points
of `V` are norms of nonzero elements of `E`, hence integer powers of `‖ϖ‖`,
which supplies the uniform factor. To improve an approximation `v`, write
`‖x - v‖ = ‖ϖ‖ ^ j` with `j = e k + t` and `0 ≤ t < e`, and put
`c = πU ^ k * ϖ ^ t` so that `u = (x - v) / c` has norm one. The lifting and
Krasner steps give an `M`-th root of unity `ζ ∈ F⟮u⟯ ⊆ E` with `‖u - ζ‖ < 1`.
Since `ζ ∈ S ⊆ U`, the element `v + ζ c` belongs to `V` and its distance to
`x` is `‖c‖ * ‖u - ζ‖ < ‖x - v‖`. Thus `E`, `V` and `U⟮ϖ⟯` have the same
underlying subset of `Ω`. The degree `m` of `ϖ` over `U` is at most `e` by
the spanning bound on `V`. The constant coefficient of its minimal polynomial
has norm `‖ϖ‖ ^ m`, an integer power of `‖πU‖ = ‖ϖ‖ ^ e`. Thus `e` divides `m`
and `m = e`, so the constant coefficient has norm `‖πU‖`. The remaining
non-leading coefficients have norm less than one
(`norm_coeff_minpoly_lt_one`), hence at most `‖πU‖`. The degree is at most
the degree of `ϖ` over `F`, which is at most `d`.

## Assembly

`finite_boundedDegree` fixes `d`, the finite set `R` of roots of `X ^ M - 1` for
`M = rootOrder F d` (`nthRootsFinset`), and for every finite `S` an element
`π S` given by `exists_valueGenerator` for `F(S)` (chosen with `choose`). This
choice gives `0 < r < 1` for `r = ‖π S‖` and expresses every nonzero norm on
`F(S)` as an integer power of `r`, as required for the degree comparison in
`adjoin_eq_of_close`. The union, over `S ⊆ R` and `1 ≤ m ≤ d`, of the finite sets of
`finite_eisensteinFields` for `U = F(S)`, `r = ‖π S‖` and degree `m` is finite.
Given a finite-dimensional subextension `E` of degree at most `d`, take `S`
to be the roots in `R` lying in `E`. The lemma `exists_eisenstein_generator`
gives the required `ϖ` and degree, placing `E` in the finite union.

Characteristic zero is used for the separability required by Krasner's lemma,
both for the roots of unity and for the roots of the Eisenstein polynomials.
