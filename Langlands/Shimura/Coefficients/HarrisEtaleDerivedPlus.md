# Bounded-below derived global sections of the full Harris coefficient system

Author: Worker 13.

This internal construction applies the actual bounded-below derived section
functor of
[`EtaleDerivedSectionsPlus`](../../Geometry/EtaleDerivedSectionsPlus.md)
to the published
[`HarrisEtaleCoefficients`](HarrisEtaleCoefficients.md) system. It retains
that system's coefficient and geometric hypotheses and uses the existing
generic resolution and natural-cohomology comparisons. There is no new
direct assertion from external literature; the original Harris coefficient
provenance is documented in the imported coefficient modules.

## Parameters and scope

The parameters are those of `harrisEtaleCoefficientSystem`:

- `A : Type u` is a finite rational algebra with a rational involution `σ`;
- `L : Type u` is a number field, `W : Type u` a finite-dimensional
  `L`-module, and `ρ` an algebraic representation of `σ.baseChange L`;
- `p` is a finite place of the rationals, `U` a compact open subgroup of
  the finite-adelic points of `σ`, and `m : ℕ` is arbitrary;
- `X : Scheme.{u}` is an actual scheme, and `Y` is an equivariant diagram
  of actual etale objects over `X`, for the original
  `harrisCongruenceGroups ρ p U m`;
- every `Y.action n` satisfies the existing geometric predicate
  `IsFiniteGeometricTorsor X`.

The scalar ring is `R = HarrisCoefficientIntegers L p`. The whole stable
Harris coefficient lattice and its reductions are retained, including every
place above `p` and every exponent, including zero. No hypothesis `m ≠ 0`
is introduced: the imported finiteness results that require it are not used
here. The supplied genuine torsor hypotheses provide the proved comparison
isomorphisms used in the coefficient system. They are not hypotheses
assuming a cohomology or derived compatibility theorem.

The sheaf and module derived categories have independent choices
`[HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X R)]` and
`[HasDerivedCategory.{wT} (ModuleCat.{u} R)]`. Mathlib's standard choices
are available. Cochain degrees are integers; nonnegative cohomology is
indexed by a natural `q`, independently of the coefficient exponent.

## Actual derived system and representative maps

Write `C = harrisEtaleCoefficientSystem ρ p U m X Y hY` and
`D = EtaleDerivedSectionsPlus.derivedSections X R`.
`harrisEtaleDerivedPlusSystem` is the actual composite

```text
C ⋙ D : ℕᵒᵖ ⥤ DerivedCategory.Plus (ModuleCat R).
```

Thus each coefficient sheaf is placed in degree zero and right-derived
global sections are applied, with the genuine coefficient transitions.
This produces a diagram of derived objects, rather than an unspecified
family of cohomology groups.

`harrisEtaleDerivedPlusComplex n` is an actual bounded-below
integer-indexed cochain complex: sections of the chosen injective
resolution of `C.obj n`, extended by zero in negative degrees.
`harrisEtaleDerivedPlusSystemIso n` identifies its localization with the
derived object at that exponent, with direction from the derived object
to the localized complex.

`harrisEtaleDerivedPlusComplexMap f` applies sections to the chosen
resolution lift of the actual sheaf transition `C.map f`.
`harrisEtaleDerivedPlusSystemIso_hom_naturality` proves that localization
of this map agrees with the derived system map under the two representative
isomorphisms. It uses the generic naturality of those comparisons.
The raw chosen complexes and lifts are not asserted to form a strict
cochain-complex-valued functor. Their maps are functorial after localization
by the proved comparison to `harrisEtaleDerivedPlusSystem`.

`harrisEtaleDerivedPlusSystem_map` expands every transition as the derived
image of `etaleAssociatedReduction`, followed by the derived image of the
inverse of `etaleAssociatedComparisonIso`. The proof is functoriality and
the existing definition of the sheaf transition. It preserves the original
coefficient reduction and the direction of the geometric torsor comparison.

## Natural cohomology recovery

For every `q : ℕ`, `harrisEtaleDerivedPlusCohomologyIso q` is a natural
isomorphism of whole inverse systems:

```text
harrisEtaleDerivedPlusSystem ⋙ Plus.homologyFunctor (ModuleCat R) q
  ≅ harrisEtaleCohomologySystem q.
```

It is the associator followed by the whiskering of the natural comparison
from `EtaleDerivedSectionsPlus.homologyNatIso`. In particular it recovers
maps as well as objects. The explicit
`harrisEtaleDerivedPlusCohomologyIso_hom_naturality` equation identifies
the map on degree-`q` derived cohomology with the original ordinary
cohomology maps of the reduction and inverse torsor comparison, in that
order. Its proof expands the target of the naturality square using
`harrisEtaleCohomologySystem_map`.

`harrisEtaleDerivedPlusZeroIso` composes this in degree zero with the
published `harrisEtaleCohomologyZeroIso` to recover the actual
`harrisEtaleSectionsSystem`. For every coefficient exponent and integer
`q < 0`, `harrisEtaleDerivedPlus_isZero_homology_of_neg` gives negative
cohomology vanishing by the generic derived-section result.

## Remaining obligations

This is ordinary derived global cohomology of the full coefficient system
on a supplied actual scheme and torsor diagram. It does not construct the
Harris Shimura scheme, the independently separating geometric tower, or
analytic uniformization. Compact supports, smooth or geometric/Galois
actions on these derived objects, derived inverse limits and comparisons
with their cohomology, and the representation-theoretic Ext spectral
sequence remain separate obligations. No boundedness above or
Mittag-Leffler assertion is made.
