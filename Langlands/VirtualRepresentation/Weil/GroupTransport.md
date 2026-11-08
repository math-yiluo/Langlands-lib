# Irreducible lattices along an isomorphism of topological groups

Author: Worker 84. This is a definition and construction contribution.

## Content

Fix topological groups `G` and `H` in independent universes, a carrier
universe `uV`, and an isomorphism of topological groups `e : G ≃ₜ* H`. The
module transports the published irreducible and unitary lattices of
`Langlands.VirtualRepresentation.Weil.Generic` along `e`. Here restriction
means pulling a representation of `H` back to `G` along `e`. So the maps go
from `H` to `G`.

### Classes of actual representations

In namespace `Langlands.FiniteRepresentation`:

- `restrictSubrepresentationOrderIso φ hφ A` identifies the invariant
  subspaces of `A` with those of its restriction along a surjective
  homomorphism `φ : G →* H`. Both sides consist of the same submodules.
- `isIrreducible_restrict_iff` follows: restriction along a surjective
  homomorphism preserves and reflects irreducibility.
- `classRank_restrictClass` and `restrictClass_classOf` record that the
  published class restriction `restrictClass` keeps the rank and acts on a
  class through a representative.
- `restrictSymmRestrictEquiv e A` is the identity map of the space of `A`,
  viewed as an isomorphism from the restriction of `A` along `e` and then
  along `e.symm` back to `A`.
- `continuousIrreducibleRestrict e` restricts a continuous irreducible
  representation of `H` along `e`. Continuity uses the published
  `isContinuous_restrict`, and irreducibility uses `isIrreducible_restrict_iff`.
  `continuousIrreducibleRestrictClass e` is the induced map on continuous
  irreducible classes. Its `forget` lemma identifies it with `restrictClass`,
  and its `symm_apply` and `apply_symm` lemmas show that restriction along
  `e.symm` inverts it.
- `continuousIrreducibleRestrictEquiv e n` is the resulting bijection of the
  published rank-`n` sets `ContinuousIrreducibleClasses H n` and
  `ContinuousIrreducibleClasses G n`.

### Bases and lattices

In namespace `Langlands.VirtualRepresentation.Weil`:

- `restrictBasisEquiv e : IrreducibleBasis H ≃ IrreducibleBasis G` keeps the
  positive rank and applies `continuousIrreducibleRestrictEquiv e` to the
  class. `restrictBasisEquiv_symm` identifies its inverse with
  `restrictBasisEquiv e.symm`. `underlyingClass_restrictBasisEquiv`,
  `restrictBasisEquiv_basisClass` and
  `basisContinuousClass_restrictBasisEquiv` compute the restricted class from
  the forgotten class, from a representative, and as the published continuous
  class restriction `continuousRestrictClass`.
- `isUnitaryClass_restrictBasisEquiv_iff` shows that `restrictBasisEquiv e`
  preserves and reflects the published unitary predicate `IsUnitaryClass`.
  The forward direction restricts an actual unitary representative using
  the published `isUnitary_restrict`. The converse applies the forward
  direction to `e.symm`. `restrictUnitaryBasisEquiv e` is the resulting
  bijection `UnitaryBasis H ≃ UnitaryBasis G`, with the same inverse,
  value and representative lemmas.
- `restrictLatticeEquiv e : IrreducibleLattice H ≃ₗ[ℤ] IrreducibleLattice G`
  and `restrictUnitaryLatticeEquiv e : UnitaryLattice H ≃ₗ[ℤ] UnitaryLattice G`
  are the published finite-support reindexing `reindex` along the two basis
  bijections. Their `single`, `generator`, `coefficient` and `symm` lemmas
  record that a generator goes to the generator of the restricted class, that
  the coefficient of the restricted class is the original coefficient, and
  that the inverse is restriction along `e.symm`.
- `includeUnitary_restrictUnitaryLatticeEquiv` shows that the inclusion of
  unitary lattices into the full lattices intertwines the two reindexings.
- `degree_restrictLatticeEquiv`, `unitaryDegree_restrictUnitaryLatticeEquiv`,
  `multiplicityPairing_restrictLatticeEquiv` and
  `unitaryPairing_restrictUnitaryLatticeEquiv` show that the integral degree
  and the coefficient pairings are preserved. The proofs are by
  finite-support induction and reduce to single generators, where the rank and
  the basis bijection settle the claim.

### Exact realization

- `realizeExact_restrictLatticeEquiv` shows that the published exact
  realization `realizeExact` intertwines `restrictLatticeEquiv e` with the
  published continuous restriction of exact virtual representations
  `ExactGrothendieckGroup.continuousRestrict (e : G →ₜ* H)`. On a generator
  both sides are the class of the restricted representative, by
  `realizeExact_generator` and `ExactGrothendieckGroup.restrict_ofClass`.
  Linearity gives the general case.
- `realizeExact_includeUnitary_restrictUnitaryLatticeEquiv` is the same
  statement for unitary lattices.
- `continuousRestrict_realizeExact_includeUnitary_eq_iff` states that, for a
  unitary element `y` over `H` and a unitary element `x` over `G`, the
  continuous restriction along `e` of the exact realization of `y` equals the
  exact realization of `x` exactly when `restrictUnitaryLatticeEquiv e y = x`.
  It uses the published injectivity `realizeExact_injective` and the
  injectivity of the unitary inclusion.

## Choices and scope

All maps are canonical given `e`. No choice of representatives, forms or
series enters beyond the published lattice constructions. The module makes no
statement about local Langlands parameters, Galois groups or fields. It does
not identify the published continuous restriction equivalence
`ExactGrothendieckGroup.continuousRestrictEquivalence` with the lattice maps
beyond the compatibility lemmas above.

## Sources

The construction is derived. Its purpose is the identification step of Guy
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), registered source
`henniart-2000-simple-proof`. In §3.7 (printed page 451) Henniart fixes a
continuous isomorphism `ι_0` from the completion `F_{v_0}` onto the given
p-adic field and identifies representations of the two Weil groups through
it. Together with the module `Langlands.Weil.Local.ExtensionWeilEquiv`, which
turns such a field isomorphism into an isomorphism of Weil groups, this
module turns that identification into an isometry of the unitary lattices of
§2.5-2.6 (printed pages 446-447). The facts used here, namely that restriction
along a group isomorphism preserves irreducibility, continuity, unitarity and
rank, are elementary and are proved in the module.

## Dependencies

Project imports are `Langlands.VirtualRepresentation.Weil.ExactCoefficients`,
`Langlands.VirtualRepresentation.ExactRestriction` and
`Langlands.Weil.Representation.UnitaryRestriction`. Published declarations
used by Lean name include `FiniteRepresentation.restrict`, `restrictClass`
and `restrictEquiv` (`Langlands.Weil.Representation.Restriction`),
`isContinuous_restrict` and `continuousRestrictClass`
(`Langlands.Weil.Representation.InductionContinuity`), `isUnitary_restrict`
(`Langlands.Weil.Representation.UnitaryRestriction`), `rank_restrict`,
`ExactGrothendieckGroup.continuousRestrict` and
`ExactGrothendieckGroup.restrict_ofClass`
(`Langlands.VirtualRepresentation.ExactRestriction`), `reindex`, `generator`,
`pairing` and `includeSubset` (`Langlands.VirtualRepresentation.Integral`),
the basis, lattice, degree and pairing declarations of
`Langlands.VirtualRepresentation.Weil.Generic`, `realizeExact` and
`realizeExact_generator` (`Langlands.VirtualRepresentation.Weil.ExactRealization`)
and `realizeExact_injective`
(`Langlands.VirtualRepresentation.Weil.ExactCoefficients`). Pinned Mathlib
supplies `OrderIso.isSimpleOrder_iff`, `Equiv.sigmaCongrRight`,
`Equiv.subtypeEquiv`, `Finsupp.domLCongr_single`,
`Finsupp.induction_linear` and `Finsupp.mapDomain_injective`. The environment
is Lean 4.34.0 with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
All declarations and proofs in this module are by Worker 84.
