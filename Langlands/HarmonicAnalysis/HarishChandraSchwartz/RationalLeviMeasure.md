# Haar measures and integrals on the standard Levi scheme

This derived compatibility construction relates measures and integrals on the actual
standard Levi subgroup and on the rational points of its representing Levi group scheme.
It uses the existing Schwartz spaces and canonical point equivalence.

## Source and provenance

The conventions are those of J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003): I.1, printed p.240 (PDF p.6), fixes the inherited
compact subgroup and normalizes subgroup Haar measure by its volume one; II.1.5, printed
p.252 (PDF p.18), gives the square-weight integrability conclusion; III.6, printed
pp.271–272 (PDF pp.37–38), defines the Schwartz space and convolution; VII.1, printed
p.313 (PDF p.79), defines the integral pairing. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The comparisons here are internal consequences of the published
`leviSchemePointsEquiv`, the Xi and height identities in `RationalLeviScheme`, and
`rationalLeviSchwartzEquiv`. They do not supply a new estimate from the article.

## Measure and exact normalization

Work over an arbitrary nonarchimedean local field `F`, with an affine group scheme `G`
locally of finite type, a commutative group scheme `S`, a homomorphism `i : S.toGrp ⟶ G`,
a cocharacter `ν`, and a set of characters `J`. Write
`M = standardLeviPoints i ν J` and
`e = leviSchemePointsEquiv i ν J`. Thus `e` is the canonical topological group
isomorphism from `rationalPoints (Standard.leviScheme i ν J)` to the actual subgroup
`M` of `G(F)`. All point spaces carry their existing rational-point or subgroup
topologies and Borel measurable structures.

For a chosen measure `μM : Measure M`, the definition is

```text
leviSchemeMeasure i ν J μM = μM.map e.symm.
```

The measure may be arbitrary. No Haar premise is needed for the change-of-variables
identities. `map_leviSchemeMeasure` proves that mapping it back by `e` recovers
`μM` exactly, and `measurePreserving_leviSchemePointsEquiv` and its `_symm`
version give measure-preserving maps in both directions. The instance
`leviSchemeMeasure_isHaarMeasure` requires `[μM.IsHaarMeasure]` and proves that
the transported measure is Haar. The pure map and integral identities omit the
local-field and finite-type assumptions unused by their proofs.

For every subgroup `K` of `G(F)`, `leviSchemeMeasure_compact` proves

```text
leviSchemeMeasure i ν J μM (leviSchemeCompact K i ν J)
  = μM (K.subgroupOf M).
```

Here the left subgroup is the preimage of `K ∩ M` under `e`.
`leviSchemeMeasure_compact_eq_one` therefore preserves a supplied volume-one
normalization. The construction retains the chosen measure, including its scale;
it does not choose a new normalization or prove existence of a special maximal compact.

## Square weights

The generic lemmas `lintegral_squareWeight_map_equiv`,
`squareIntegrableWeight_map_equiv_iff`, and `L2Weights.map_equiv_iff` apply to
any measurable equivalence, any measure, and real-valued weights. The first preserves
the extended nonnegative integral of `Ξ² (1 + σ)^(-d)` for every real `d`.
The second preserves `SquareIntegrableWeight`, whose exponent is a natural number.
The third preserves all three fields of `L2Weights`: pointwise positivity of Xi,
nonnegativity of the height, and finiteness of the square-weight integral for some
real exponent.

The actual Levi weight comparisons have these additional explicit premises:

- `hG : IsConnectedReductive G`;
- `hi : IsMaximalSplitTorus i`, `hν : IsGenericCocharacter i ν`, and
  `hJ : J ⊆ simpleRelativeRoots i ν`;
- an open compact subgroup `K` of `G(F)`, with proofs `hKo` and `hKc`;
- a matrix representation `ρ : MatrixRepresentation G n`, where `n` is finite,
  decidable and nonempty;
- the Levi Iwasawa factorization
  `hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf M)
    (K.subgroupOf M)`.

There is no faithfulness or closed-embedding premise on `ρ`. The restricted
representation on the scheme is `ρ.restrict (Standard.leviHom i ν J)`.
The scheme's compact subgroup and Iwasawa pair are the published transports of
`K ∩ M` and `hM`.

`lintegral_squareWeight_leviSchemeMeasure` identifies the integral with the
scheme's `rationalXi` and restricted-representation height with that for
`rationalLeviXi hKc hM` and the ambient `rationalHeight ρ` restricted to `M`,
for each real exponent. `squareIntegrableWeight_leviSchemeMeasure_iff` gives
the corresponding equivalence of the natural-exponent II.1.5 conclusions.
`l2Weights_leviSchemeMeasure_iff` gives the equivalence of the full `L2Weights`
hypotheses. These equivalences transfer supplied estimates in either direction;
they do not prove II.1.5 or discharge `hM`.

## Pairing, norms and convolution

For arbitrary complex-valued functions `f₁, f₂` on `M`,
`pairing_leviSchemeMeasure` identifies their pairing on `M` with the pairing of
`f₁ ∘ e` and `f₂ ∘ e` on the scheme points. The generic
`pairing_map_equiv` is the measurable-equivalence version. Pairing means the
Bochner integral `∫ conj(f₁) * f₂`, with the existing total-integral convention.

`eLpNorm_leviSchemeMeasure` preserves the extended `Lᵖ` norm for every
`p : ℝ≥0∞`, and `memLp_leviSchemeMeasure_iff` preserves `MemLp` in both
directions, including its measurability requirement. In particular this applies
to `p = 2`.

With convolution defined by `∫ y, f₁(y) f₂(y⁻¹ x)`, the generic
`convolution_map_continuousMulEquiv` and its specialization
`convolution_leviSchemeMeasure` prove pointwise compatibility. For scheme point
`x`, the latter identity is

```text
convolution (leviSchemeMeasure i ν J μM) (f₁ ∘ e) (f₂ ∘ e) x
  = convolution μM f₁ f₂ (e x).
```

This identity uses the total Bochner integral and therefore holds even without
an integrability premise. Separately,
`integrable_convolution_leviSchemeMeasure_iff` proves equivalence of integrability
of the two displayed convolution integrands. It transfers absolute convergence
when it has been established on either side.

Under the weight premises above, `pairing_rationalLeviSchwartzEquiv`,
`eLpNorm_rationalLeviSchwartzEquiv`, and
`convolution_rationalLeviSchwartzEquiv` specialize these identities to the
existing Schwartz equivalence. Norm and pairing preservation alone do not assert
that every Schwartz function is in `L²` for an arbitrary chosen measure.
The existing `L2` theory supplies this conclusion when `L2Weights` is available;
the weight equivalence above transports that hypothesis.

## Implemented proof and scope

The proofs apply Mathlib's measurable-equivalence change-of-variables identities
to `e` or its inverse. Haar transport uses the topological group isomorphism.
The compact-volume proof identifies the exact preimage subgroup. The weight proofs
rewrite by the published `rationalXi_leviScheme` and
`rationalHeight_restrict_leviHom` identities. Multiplication and inversion
preservation identify the two convolution integrands. The Schwartz specializations
use the published pointwise formula for `rationalLeviSchwartzEquiv`.

No characteristic-zero, splitness or quasisplitness assumption is imposed.
The Levi Iwasawa factorization remains explicit. This unit establishes no new
integrability estimate, convolution closure or continuity theorem, density result,
formal-degree normalization, spectral transform, or Plancherel inversion.
