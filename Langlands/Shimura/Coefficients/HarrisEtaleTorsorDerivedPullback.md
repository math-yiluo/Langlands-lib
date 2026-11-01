# Derived Harris pullback to the actual associated geometric target

This module combines the actual
[derived geometric pullback](HarrisEtaleDerivedPullback.md) with the proved
[Harris coefficient comparison](HarrisEtaleTorsorPullback.md). Its target is
derived sections of the full Harris system associated independently to the
geometrically pulled-back torsors.

## Inputs and derived categories

The algebraic representation, number field, rational finite place, compact open
level and natural-number reduction scalar `m` are those of
`harrisCoefficientDiagram ρ p U m`. Write
`R = HarrisCoefficientIntegers L p` and
`I = harrisCoefficientScalarIdeal L p m = Ideal.span {(m : R)}`.
The diagram index `op n` gives the full stable lattice reduced modulo `I^n`;
`m` does not select a starting exponent. All coefficient places and all
exponents `n`, including zero, are retained. An actual scheme `X`, compatible
Harris cover diagram `Y`, and finite-geometric-torsor proofs `hY` are supplied.

The map `f : Z ⟶ X` is etale. `Yf` denotes the actual
`etaleTorsorDiagramPullback f _` applied to `Y`, and `hYf` denotes its constructed
finite-torsor proofs. The comparison is therefore with the existing Harris
constructions applied independently to `Z,Yf,hYf`.

Schemes, algebra, coefficient fields, representations, groups and module
carriers share universe `u`. Derived-category instance universes `wX`, `wZ`
and `wT` are independent. The module requires `HasDerivedCategory` for the
small-etale module-sheaf categories on both schemes and for `ModuleCat R`,
where `R = HarrisCoefficientIntegers L p`. The resulting objects lie in
Mathlib's bounded-below derived category. No strictly functorial choice of
resolution maps is assumed.

## Construction and transitions

`harrisEtaleTorsorDerivedPlusIso` applies actual derived global sections on `Z`
to the whole coefficient-system isomorphism
`harrisEtaleCoefficientSystemPullback`. It identifies the previously defined
restricted derived system with `harrisEtaleDerivedPlusSystem` on `Z,Yf,hYf`.

`harrisEtaleTorsorDerivedPlusPullback` composes the already constructed derived
geometric map with this target isomorphism. Its `app` equation identifies each
component as

```text
geometric derived pullback
  followed by derivedSections_Z.map(canonical associated-sheaf comparison).
```

This is a natural transformation of full `ℕᵒᵖ` diagrams.
`harrisEtaleTorsorDerivedPlusPullback_naturality` records its square with every
original and new transition. Each system retains coefficient reduction followed
by the inverse of the proved finite-torsor cover comparison.

The target identification is an isomorphism. The geometric derived pullback
itself is a morphism; its invertibility is not asserted.

## Recovery under the specified canonical comparisons

For every `q : ℕ`, `harrisEtaleTorsorDerivedPlusIso_homology q` proves that
homology of the derived target identification, followed by the existing
canonical Harris cohomology isomorphism on `Z`, equals the restricted-system
cohomology isomorphism followed by `harrisEtaleTorsorCohomologyIso q`.
The proof evaluates at each exponent and uses naturality of the actual
`EtaleDerivedSectionsPlus.homologyNatIso` at the constructed coefficient map.

`harrisEtaleTorsorDerivedPlusIso_zero` proves the corresponding section square
using `homologyZeroIso`. It first identifies the existing Harris degree-zero
comparison with `systemDerivedSectionsZeroIso`, so the assertion concerns the
specified canonical comparison, rather than the existence of some isomorphism.

`harrisEtaleTorsorDerivedPlusPullback_homology q` then gives the whole-map square

```text
H^q(derived geometric pullback to the actual associated target)
  ; canonical cohomology comparison on Z
 =
canonical cohomology comparison on X
  ; harrisEtaleTorsorCohomologyPullback q.
```

`harrisEtaleTorsorDerivedPlusPullback_zero` similarly recovers
`harrisEtaleTorsorSectionsPullback` under the original degree-zero Harris
comparisons. Both proofs compose the target-identification square with the
previously proved recovery for geometric maps to restricted sheaves.

## Provenance and boundaries

This is an internal derived-functor construction. The coefficient comparison,
geometric pullback and canonical recovery maps are constructed project inputs;
no desired output comparison or recovery equation is assumed. Whiskering and
composition form the new maps, and naturality proves their intrinsic recovery
obligations. No new theorem is attributed to Harris or other literature here.

The actual Shimura schemes and Harris torsors remain supplied geometry.
This treats one etale base change. Coherence for successive associated
geometric base changes, arbitrary non-etale or algebraic-closure inverse image,
compact supports, smooth or Galois actions, adic or rational limits,
spectral-sequence degeneration and the local-global comparison remain separate.
