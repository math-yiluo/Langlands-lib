# Potential semiabelian reduction from Néron existence and Raynaud's criterion

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.PotentialSemistableReductionFromRaynaudStatement` is

`NeronModelExistenceStatement.{u} → RaynaudSemiabelianCriterionStatement.{u} → PotentialSemistableReductionStatement.{u}`.

The three propositions are Library statements in `Langlands/AbelianScheme/`.

- `NeronModelExistenceStatement`: every abelian variety over the fraction
  field of a discrete valuation ring has a Néron model with its generic
  identification.
- `RaynaudSemiabelianCriterionStatement`: if `n ≥ 3` is a unit of the
  valuation ring and all `n`-torsion points over an algebraic closure are
  rational, every Néron model has semiabelian geometric special identity
  component.
- `PotentialSemistableReductionStatement`: after a finite extension of the
  fraction field and a local extension of discrete valuation rings, the
  base change has a Néron model with semiabelian geometric special
  identity component.

The theorem `potentialSemistableReductionFromRaynaud` proves the reduction.

## Proof

Fix `V`, `K` and an abelian variety `B` over `K`.

- `exists_three_le_isUnit_natCast` gives `n ∈ {3, 4}` that is a unit of
  `V`. If `3` is not a unit of the local ring `V`, then `4` is one, since
  `4 + (-3) = 1` and `IsLocalRing.isUnit_or_isUnit_of_isUnit_add` makes one
  of the two summands a unit.
- The image of `n` in `K` is a unit. The Library theorem
  `exists_finite_hasRationalGeometricTorsion`, from
  `Langlands/AbelianScheme/RationalTorsionExtension.lean`, gives a finite
  extension `L` of `K`. Over `L` all `n`-torsion points of the base change
  of `B` over an algebraic closure are rational.
- `FiniteDvrExtension.ofFiniteField V K L` (from
  `Langlands/AbelianScheme/SemistableReductionConstruction.lean`) is a
  discrete valuation ring `W` dominating `V` with fraction field `L`. The
  map `V → W` sends units to units, so `n` is a unit of `W`.
- `NeronModelExistenceStatement` for `W`, `L` and the base change of `B`
  gives a Néron model `N`. `RaynaudSemiabelianCriterionStatement` applied
  to `N` and `n` gives its semiabelian geometric special identity
  component. The extension `W` and the model `N` witness
  `PotentialSemistableReductionStatement`.

## Provenance

The route deduces the semistable reduction theorem from Raynaud's
criterion, applied after a finite extension that makes the `n`-torsion
rational. Silverberg and Zarhin, *Semistable reduction and torsion
subgroups of abelian varieties*, Ann. Inst. Fourier 45 (1995), §3, printed
pp. 405–406, state the semistable reduction theorem as Theorem 3.4 and
Raynaud's criterion as Theorem 3.5. The target is the form of Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4, printed p. 181,
Theorem 1, recorded in
`Langlands/AbelianScheme/PotentialSemistableReductionStatement.md`. The
Néron model input is Bosch, Lütkebohmert and Raynaud, §1.3, printed p. 16,
Corollary 2. This module proves only the implication. It does not prove
either input.
