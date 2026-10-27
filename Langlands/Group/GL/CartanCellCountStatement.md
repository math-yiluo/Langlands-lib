# Counting left cosets in an antidominant Cartan double coset

Author: Worker 246.

This pair defines one closed proposition,
`Langlands.GeneralLinear.CartanQuotient.CartanCellCountStatement.{uF}`, using
the published definitions of
[`Langlands.Group.GL.CartanQuotientDefinitions`](CartanQuotientDefinitions.md).
It is a `Prop`-valued definition; nothing is proved here.

## Exact statement

The proposition quantifies every natural prime `p` with `[Fact p.Prime]`,
every `F : PadicField.{uF} p`, every supplied `T : F.TopologicalData` and every
rank `n : ℕ`; rank zero is allowed. It asserts a real constant `c` such that,
for every `lam : Fin n → ℤ` with `Antitone lam`, there is a finite set
`R : Finset (GeneralLinear n F.Carrier)` with

```text
(R.card : ℝ) ≤ c * (delta T lam)⁻¹
```

and such that for all `k₁, k₂ ∈ K` there are `r ∈ R` and `k ∈ K` with

```text
k₁ * representative T lam * k₂ = r * representative T lam * k.
```

Thus `K a(lam) K ⊆ ⋃_{r ∈ R} r a(lam) K`. The constant may depend on
`p, F, T, n`, but not on `lam`.

The objects have their published concrete meanings:

- `K = maximalCompact T n`, which is
  `Iwasawa.integralRange T.discreteValuation n`, the image of `GL_n(O_F)`.
- `representative T lam = a(lam)` is
  `Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam`, the
  diagonal matrix `diag(ϖ^(lam 0), …, ϖ^(lam (n-1)))` for the specified
  uniformizer `ϖ`.
- `delta T lam = q^(-degree lam)`, where `q = T.residueCardinality` and
  `degree lam = ∑_{i<j} (lam i - lam j)`. For antitone `lam` the degree is
  nonnegative, so `(delta T lam)⁻¹ = q^(degree lam) ≥ 1`.

Only `Antitone` is required, not `Normalized`: a common shift of `lam` changes
neither `delta T lam` nor the coset geometry, since it multiplies `a(lam)` by
a central scalar. No Haar measure, topology, measurability or quotient by the
centre enters the statement. The elements of `R` are not required to lie in
`K`, although the natural proof chooses them there. The statement gives only
an upper bound; it asserts no lower bound and no disjointness of the
translates.

## Intended use

For any left Haar measure, `r a(lam) K` has the same measure as `K`, so the
statement bounds the (outer) measure of the Cartan double coset
`K a(lam) K`, and of its image cell in `GL_n(F)/Z`, by
`c * mes(K) * delta(lam)⁻¹`. This is the upper half of Waldspurger's estimate
quoted below. The product-Levi tempered sufficiency proof of task
`ea9d1814-a777-42a1-9bf7-29b9b44dc87e` uses the statement in this
left-translate form, which needs no measure-theoretic statement about
double cosets. The upper half of the two-sided volume statement anticipated
by task `9f05c6f1-4c4f-4469-b8ee-5290c73fc9ce` should also follow from it.

## Provenance (derived specialization)

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
§I.1, equation (5) and its proof, printed pp.241–242 (PDF pages 7–8).
Source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`, retained
at
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
No errata note for this passage was found in the public Library notes or
project notes.

Equation (5) asserts constants `C₁, C₂ > 0` with
`C₁ δ₀(m)⁻¹ ≤ mes(KmK) ≤ C₂ δ₀(m)⁻¹` for `m` in the closed positive chamber
`M̄₀⁺`, where `δ₀ = δ_{P₀}`. With the sign convention
`q^(-⟨χ, H(g)⟩) = |χ(g)|` of printed p.240, for the upper Borel of `GL_n` the
closed positive chamber consists of diagonal matrices with
`|m_i / m_j| ≤ 1` for `i < j`; for `m = a(lam)` this is `Antitone lam`, and
`δ₀(a(lam)) = ∏_{i<j} |ϖ^(lam i - lam j)| = delta T lam`.

The proof on pp.241–242 fixes a subgroup `H ⊆ K` with an Iwahori
factorization and writes `mes(HmH) = mes(H) [H : mHm⁻¹ ∩ H]`, where the index
factors as `c_{U₀}(m) c_{M₀}(m) c_{Ū₀}(m)` with
`c_{U₀}(m) = δ₀(m)⁻¹ c'_{U₀}(m)` and the remaining terms bounded integers.
The present statement is the corresponding index form: `K a K` is the
disjoint union of the `[K : K ∩ aKa⁻¹]` translates `k a K`, and
`[K : K ∩ aKa⁻¹] ≤ [K : H] · [H : H ∩ aHa⁻¹]`. The integer formulation, the
restriction to the standard integral subgroup of `GL_n`, and the
left-translate covering form are derived specializations; Waldspurger states
the measure inequality for a general connected reductive group.

## Remaining proof obligation

A proof may take `H` to be the principal congruence subgroup
`1 + ϖ M_n(O_F)`. It has finite index in `K`, and its Iwahori factorization
`H = (H ∩ N̄)(H ∩ M₀)(H ∩ N)`, with `N` upper and `N̄` lower unipotent,
gives `H ∩ aHa⁻¹ = (H ∩ N̄)(H ∩ M₀)(a(H ∩ N)a⁻¹)` for `a = a(lam)` with
antitone `lam`: conjugation by `a⁻¹` fixes the diagonal part and maps `H ∩ N̄`
into itself, while conjugation by `a` maps `H ∩ N` into itself. Hence
`[H : H ∩ aHa⁻¹] = [H ∩ N : a(H ∩ N)a⁻¹]`. Conjugation by `a` multiplies the
upper entry `(i, j)`, `i < j`, by `ϖ^(lam i - lam j)`, so the last index is
`∏_{i<j} q^(lam i - lam j) = q^(degree lam)`. These index computations, the
Iwahori factorization and the finiteness of `[K : H]` are not assumed here
and remain to be proved.
