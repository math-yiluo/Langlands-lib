# Dense unitary irreducibility of actual common-Levi normalized induction

Module `Langlands.Representation.Plancherel.ActualCommonLeviUnitaryIrreducibilityStatement`,
namespace `Langlands.Plancherel.ActualCommonLeviV3`. The primary declaration is
the Prop-valued statement `DenseUnitaryIrreducibilityStatement`. It is
unproved here.

## Statement

The data are those of `ActualCommonLeviV3Statement`:

- a nonarchimedean local field `F` (universe `u`);
- an affine locally finite type group scheme `G` over `F`;
- a cocharacter `χ` with common Levi `levi χ`;
- a smooth complex representation `A` of `levi χ` (carrier universe `uV`);
- a normal central subgroup `C` and a Haar measure `qMeasure` on
  `levi χ ⧸ C`.

The statement's explicit arguments are `χ`, `A`, `C`, `hC` and `qMeasure`.
Its instance arguments are normality of `C`, the measurable structure on
`levi χ ⧸ C` and the Haar property of `qMeasure`. The Borel and
inversion-invariance instances declared in the module are not used by the
proposition, so Lean does not make them arguments. Its body has four
premises:

- `IsConnectedReductive G`;
- `IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure`;
- `A.representation.IsIrreducible`;
- the actual split-center identification `IsActualSplitCenter χ C`.

Under these premises, it asserts the following for every cocharacter `ψ`
whose actual dynamic centralizer equals that of `χ`. Consider the unitary
unramified parameters `z` (`unitaryUnramifiedCharacters (normCharacters χ)`)
at which the actual normalized induction
`(normalizedInductionFunctor (commonDecomposition χ ψ hψ) (radical_isClosed ψ)).obj
(twistObject χ (unitaryParameter χ z) A)` is irreducible. These form a dense
subset of the unitary parameter group, for its subspace topology.

No compact open subgroup, Iwasawa factorization or regularity condition is
assumed.

## Provenance

Derived from J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), source `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:

- Proposition IV.2.2(i), printed p.284 / PDF p.50: if `π` is irreducible,
  square integrable and `G`-regular, then `I_P^G π` is irreducible.
- IV.3, printed p.285 / PDF p.51: for `π` square integrable, IV.2.2 gives a
  point `π'` of the unramified orbit `O_C` with `I_P^G π'` irreducible. The set
  of such points is then a nonempty Zariski open subset of `O_C`.

The source does not state density in the unitary part. The statement here
combines these results with the fact that a nonempty Zariski open subset of
the complex parameter torus meets the compact unitary subtorus in a dense
set. Alternatively, IV.2.2(i) gives the density once the `G`-regular unitary
twists are known to be dense. This
derived formulation is what the coefficient-injectivity route of
`ActualCommonLeviCoherenceReduction` needs.
