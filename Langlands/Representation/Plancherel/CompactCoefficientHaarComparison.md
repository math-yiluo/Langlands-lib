# Actual compact coefficients with spherical Haar normalization

This internal construction compares the intrinsic Haar probability used for
compact normalized-induction duality with the Haar probability used for the
spherical function. It then constructs the integral of the actual
product-induced diagonal contraction with that spherical normalization and
identifies it with the existing compact coefficient map.

The source conventions are Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), I.1, printed page 240
(PDF page 6), and II.1, printed page 251 (PDF page 17). The registered source is
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.1 fixes Haar mass one on the compact subgroup; II.1 defines the spherical
function by its integral on that subgroup. The equality here is a deduction
from uniqueness of Haar probability, rather than a separately asserted theorem
in the source. The connection to the spherical integral was proposed by
Worker 249; Worker 200 implemented this comparison.

## Measures and hypotheses

The measure comparison uses a topological group `G`, its Borel measurable
structure, and a compact open subgroup `K`.
The explicit instance `[CompactSpace K]` supplies compactness for the spherical
measure, and `hK : IsCompact (K : Set G)` supplies the ambient compactness proof
used by `CompactInduction.measure`. These are two forms of the same compactness
property, not two choices of measure.

`measure_eq_normalizedHaar` proves the literal equality

```text
CompactInduction.measure K hK =
  HarishChandraSchwartz.normalizedHaar (K : Subgroup G).
```

The first measure is the comap along the inclusion of `K` of the already
constructed ambient Haar measure giving `K` mass one. The second is Mathlib's
Haar measure on the compact group `K` normalized on the whole group. Existing
instances say that both are Haar and probability measures. The proof applies
`Measure.isHaarMeasure_eq_of_isProbabilityMeasure` to these exact measures.
It introduces no scaling factor or new measure choice.

## The actual integral map

The integral construction uses a locally compact nonarchimedean group with its
Borel structure, actual subgroups `P`, `M`, `U`, a semidirect decomposition
`h : IsSemidirectDecomposition P M U`, closed `U`, a canonical
`SmoothRep ℂ M` object `A`, and compact open `K`. The group universe `uG` and
representation-carrier universe `uV` are independent. No admissibility,
irreducibility, global `P K` factorization or modulus comparison is needed
to define this integral.

Its domain is the existing `productInducedCoefficientObject h hU A`, the
actual normalized smooth induction from `P × P` to `G × G` of the tensor
of `A` with its smooth contragredient. For a vector `F` in that original
induced-function carrier, `integrand h hU A K g F k` is the existing scalar
contraction of `F(k g, k)`. The contraction evaluates the smooth functional
on the vector and is complex bilinear, with no conjugation.

`integrand_normalizedHaar_integrable` proves integrability of this function
of `k` for every `F` and `g`: existing local constancy gives continuity,
and compactness of `K` gives compact support. It uses spherical Haar
probability directly.

`sphericalCoefficientIntegral` is the linear map from this product-induced
object to `G → ℂ` given by

```text
sphericalCoefficientIntegral F g = ∫ k : K, integrand g F k d(normalizedHaar K).
```

Its additivity follows from additivity of the existing diagonal contraction,
the two proved integrability statements and `integral_add`. Its complex scalar
law follows from the contraction's scalar law and `integral_smul`. Thus this
is a constructed integral on the original carrier.

## Comparison with the coefficient construction

`coefficientMap_eq_sphericalCoefficientIntegral` retains the existing compact
coefficient map's hypotheses: in addition to the integral data, `G` is
Hausdorff and second countable, `P` is locally compact and closed, the Levi
projection is continuous, `G = P K`, `G` has trivial modular character,
and the modular character of `P` equals the actual Haar modulus of its
conjugation action on `U`. The inducing representation `A` is admissible.
These are visible parameters of the theorem. There is no irreducibility
assumption on the inducing or induced representation.

For every original product-induced `F` and every `g : G`, it proves

```text
coefficientMap F g = sphericalCoefficientIntegral F g.
```

The proof starts from the existing `coefficientMap_integral` formula and
rewrites its measure by `measure_eq_normalizedHaar`. It therefore preserves
the diagonal evaluation order `(k g, k)`, the actual coefficient tensors,
the compact-duality normalization and the original induced carrier.

## Scope

This supplies the exact normalization comparison needed when applying a
spherical-Haar integral estimate to the actual compact coefficient map.
It does not identify the earlier arbitrary-scale Bruhat measure with Haar
probability. Identification of a supplied `K` with the source's special
compact subgroup, realization of the displayed structural inputs,
independence of `K`, the Levi coefficient estimates, uniformity in unitary
unramified families, the remaining assembly of VI.2.2, and the Plancherel
theorem remain separate obligations.
