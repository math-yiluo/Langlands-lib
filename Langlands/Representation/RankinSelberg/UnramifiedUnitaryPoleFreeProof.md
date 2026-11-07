# Proof of the unitary pole bound for unramified pairs

Author: Worker 1797. Module
`Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof`.

```lean
theorem Langlands.RankinSelberg.unramifiedUnitaryPoleFree :
    UnramifiedUnitaryPoleFreeStatement.{uF, uV, uW}
```

This proves the unchanged Library proposition
`Langlands.RankinSelberg.UnramifiedUnitaryPoleFreeStatement` (module
`Langlands.Representation.RankinSelberg.UnramifiedPairStatement`), which is conjunct (C) of
`UnramifiedPairStatement`. The proposition is: for every prime `p`, every p-adic field `F`
with its canonical topology, and naturals `n < t`, let `π` (on `GL_(t+1)(F)`) and `σ` (on
`GL_(n+1)(F)`) be unramified generic constituents (`IsUnramifiedGenericConstituent`) with
inducing characters `χ`, `χ'`, for the same nontrivial unitary additive character `ψ`.
If both are unitarizable (`IsUnitarizable`: an invariant positive definite Hermitian
form), then for every `s` with `1 ≤ Re s`,

`∏_i ∏_j (1 - a_i b_j q^(-s)) ≠ 0`, where `a = unramifiedClass F χ`,
`b = unramifiedClass F χ'`, and `q` is the residue cardinality.

No hypothesis is added. Arbitrary `ψ` is allowed (no conductor assumption), every `n < t`
is allowed (including `σ` of rank one), and unitarizability is the actual invariant
positive form.

## Source

Jacquet–Shalika, *On Euler products and the classification of automorphic forms II*,
Amer. J. Math. 103 (1981), Proposition 1.5(iii), printed p. 782 (literature id
`jacquet-shalika-1981-euler-products-ii`). The source deduces the absence of poles from
the convergence for `Re s ≥ 1` of the integrals `Ψ(s, W, W')` for unitary generic
representations, combined with the unramified computation `Ψ(s, W₀, W₀') = L(s, π × σ)`.
That convergence rests on Euler products I, Proposition (1.3), printed pp. 505–507: the
`L²` property of Whittaker functions on the mirabolic subgroup.

## Implemented route

The proof does not use the integral formula of conjunct (B). It derives the bounds
`|a_i| < q^(1/2)` and `|b_j| ≤ q^(1/2)` from the same `L²` mechanism, and then concludes
by an elementary estimate.

1. **`L²` on cells** (`UnitaryCellBound`): an algebraic version of Euler products I,
   Proposition (1.3). It uses Kirillov injectivity (`UnramifiedKirillovInjectivity`),
   Bernstein–Zelevinsky compact minimality, the published forms-to-functionals injection,
   Whittaker multiplicity one, the Hermitian smooth dual and Cauchy–Schwarz.
2. **Masses of single-row cells** (`UnitaryCellMasses`): `ν(N t_m K) ≥ q^(k m)` for
   `t_m = diag(ϖ^m, 1, …, 1)` in `GL_(k+2)`, hence `∑_m q^(k m) |W₀(t_m)|² < ∞`.
3. **Exponent bound** (`UnitaryExponentBound`): Worker 1767's published single-row Shintani
   value `W₀(t_m) = q^(-(k+1)m/2) h_m(a)` gives `∑ q^(-m) |h_m(a)|² < ∞`, and a power-series
   argument gives `|a_i| < q^(1/2)` when `ψ` has conductor `O`.
4. **This module**: removal of the conductor hypothesis, the rank-one case, and the final
   estimate.

## Declarations of this module

Namespace `Langlands.RankinSelberg.UnramifiedUnitary`, with the canonical topology,
valuation and local-field structure of `F` as local instances.

- `discreteValuation_eq_exp_neg_ord`, `mem_integers_iff_ord`,
  `mem_additiveLattice_iff_ord`: for `x ≠ 0`, membership in the integers and in the
  fractional ideals `T.additiveLattice n = ϖ^(-n) O` read off the order `T.ord x`.
- `exists_scale_hasIntegerConductor`: every nontrivial unitary additive character `ψ` has a
  scaling `ψ.scale a` (`x ↦ ψ(a x)`) of conductor `O`. Take `a = ϖ^(-c)`, where
  `c = T.additiveConductor ψ` is the published largest `n` with `ψ` trivial on
  `ϖ^(-n) O`. Then `ψ(a O) = ψ(ϖ^(-c) O) = 1`. Conversely, suppose `x ∉ O`, so
  `ord x ≤ -1`. Take `z ∈ ϖ^(-c-1) O` with `ψ(z) ≠ 1`
  (`exists_nontrivial_at_conductor_succ`). Then `y = z/(a x)` has `ord y ≥ 0`, and
  `ψ(a x y) = ψ(z) ≠ 1`.
- `isUnramifiedGenericConstituent_scale`: the constituent property for `ψ` gives it for
  `ψ.scale a`. Only the Whittaker functional changes; the published
  `characterChangeFunctional` (`ℓ ∘ π(diag(a^n, …, 1))`) is nonzero when `ℓ` is.
- `norm_unramifiedClass_rankOne`: for a unitarizable unramified generic constituent `σ` of
  `GL_1(F)`, `|b_0| = 1`. After scaling `ψ` to conductor `O`, take the normalized spherical
  test `w` of conjunct (A) and a `GL_1(O)`-fixed vector `v` with coefficient function `w`,
  so `ℓ(v) = 1`. The published `sphericalTest_torus_schur` at the exponent `(1)` gives
  `ℓ(σ(ϖ) v) = b_0`. Since `GL_1` is commutative, `σ(ϖ) v` is spherical. The spherical line
  (`UnramifiedWhittaker.fixedLine_of_isGeneric`) then gives `σ(ϖ) v = c v`, and applying
  `ℓ` gives `c = b_0`. Invariance of the positive form gives
  `|b_0|² b(v, v) = b(v, v)` with `b(v, v) ≠ 0`.
- `norm_unramifiedClass_lt_sqrt`: in rank `k+2`, `|a_i| < √q` for every `ψ`. This is
  `norm_characterValues_lt_sqrt` applied after scaling `ψ` to conductor `O`. The Satake
  parameters `unramifiedClass F χ` and the published `characterValues F χ` are the same
  uniformizer values.
- `norm_unramifiedClass_le_sqrt`: in every rank `n+1`, `|b_j| ≤ √q`. In rank one
  `|b_0| = 1 ≤ √q` since `q ≥ 2`; in higher rank, use the previous item.

## The final theorem

Write `t = k + 1` (possible since `n < t`). For `Re s ≥ 1`,
`|q^(-s)| = q^(-Re s) ≤ q^(-1)` (`Complex.norm_natCast_cpow_of_pos`,
`Real.rpow_le_rpow_of_exponent_le`). Since `π` has rank `k + 2 ≥ 2`, `|a_i| < √q`. For
`σ`, `|b_j| ≤ √q`. Hence `|a_i b_j| < q` and `|a_i b_j q^(-s)| < 1`. So no factor
`1 - a_i b_j q^(-s)` vanishes, and neither does their product (`Finset.prod_ne_zero_iff`).

## Helper modules

The candidate ships these helper modules, each with its own Markdown:
`UnramifiedKirillovInjectivity`, `UnitaryCellBound`, `UnitaryCellMasses` and
`UnitaryExponentBound`. The proof uses conjunct (A)
(`Langlands.RankinSelberg.unramifiedSphericalVector`) and Worker 1767's
`SphericalWhittakerFormula`, both published in the Library.
