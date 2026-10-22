# Character conductors under a p-adic algebra equivalence

Author: Worker 20. This module constructs character transport for the canonical
local-field topologies and proves compatibility of the existing conductor
constructions. All declarations are in
`Langlands.PadicField.ConductorTransport`.

## Inputs and actual character maps

Fix a prime `p`, finite p-adic fields `F` and `E` in independent universes,
and an actual algebra equivalence `e : F.Carrier ≃ₐ[Padic p] E.Carrier`.
The topologies, discrete valuations and conductor definitions throughout are
those of `F.canonicalTopologicalData` and `E.canonicalTopologicalData`.

`unitsEquiv F E e` is the continuous multiplicative equivalence on the actual
field-unit groups induced by `e`. Its underlying equivalence is
`Units.mapEquiv e.toMulEquiv`. The already published `extension_isometry`
proves continuity of both field maps; continuity of their induced unit maps
follows from Mathlib's `Continuous.units_map`. The two application lemmas
identify the underlying field values with `e` and `e.symm`, respectively.

`additiveCharacter F E e ψ` is the existing
`HarmonicAnalysis.FieldTransport.additiveCharacter` specialized to this field
map and its proved inverse continuity. Thus it sends `ψ` to `ψ ∘ e.symm`,
retaining its continuity and nontriviality. It introduces no new additive
character type and chooses no character.

`quasicharacter F E e χ` is the continuous monoid homomorphism obtained by
composing `χ : F.Carrierˣ →ₜ* ℂˣ` with the inverse of `unitsEquiv F E e`.
Its application lemma records this exact inverse-pullback formula. No
unitarity hypothesis is imposed on a quasicharacter.

## Filtrations and extremal levels

The published additive lattice at integer level `n` consists of all `x` with
`v(x) ≤ exp n`, equivalently the fractional ideal `π^(-n) O`. The theorem
`mem_additiveLattice_map_iff` proves that `e x` belongs to the target lattice
at level `n` exactly when `x` belongs to the source lattice at that same
level. The proof substitutes the actual valuation identity
`CanonicalTransport.discreteValuation_map` into the membership condition.

`mem_principalUnits_map_iff` proves the corresponding equivalence for the
actual unit filtration at every natural level, including zero. It rewrites
both membership conditions, `v(u) = 1` and `v(u - 1) ≤ exp(-n)`, using the
same valuation identity and preservation of subtraction and one by `e`.
At level zero these are the integral units, as proved in `Conductor`.

The two triviality equivalences quantify over the whole lattice or unit
subgroup. In one direction, evaluate the transported character at the image
of an arbitrary source element. In the other direction, use surjectivity of
the actual field or unit equivalence. Inverse cancellation and the preceding
membership equivalences give both implications.

`additiveConductor_eq` proves that the transported character has the same
integer additive conductor. It uses the defining greatest-level property
on each side and the additive triviality equivalence, then antisymmetry.
`multiplicativeConductor_eq` compares the least principal-unit triviality
levels by applying the published least-level criterion in both directions.
Neither proof compares arbitrary choice witnesses or assumes equality of
conductors as transport data.

Finally `isUnramifiedQuasicharacter_iff` follows from the multiplicative
conductor equality and the published equivalence between conductor zero and
triviality on integral units. It preserves and reflects unramifiedness.

## Internal provenance and dependencies

This is internal compatibility of published constructions. No new assertion
is attributed to external literature. The source conventions and existence
proofs for the conductors remain those documented in
`Langlands/HarmonicAnalysis/Conductor.md`; this module consumes them without
changing their definitions or hypotheses.

The direct imports are:

- `Langlands.HarmonicAnalysis.Conductor`, supplying the actual filtrations,
  triviality predicates, proved conductor existence, extrema specifications,
  and the unramifiedness criterion.
- `Langlands.HarmonicAnalysis.FieldTransport`, supplying inverse pullback of
  the actual nontrivial additive characters; its imported character-transport
  construction proves nontriviality using surjectivity.
- `Langlands.LocalField.CanonicalTransport`, supplying preservation of the
  actual normalized discrete valuation; its imported
  `Langlands.Weil.Local.ExtensionResidue` supplies `extension_isometry`.

Pinned Mathlib supplies the unit equivalence, continuity of unit maps,
continuous monoid-homomorphism composition and order antisymmetry. The local
normed-field instances are the published canonical instances, and explicit
local topology instances select the exact canonical topological data used by
the conductor API.

## Scope

The comparison concerns an invertible map over the same p-adic base and the
specified canonical topological data. It does not assert invariance along a
proper field extension. It does not identify chosen uniformizers, assume
reciprocity or a self-dual measure, or construct an epsilon system. Actual
abelian-factor transport and its Haar change of variables are subsequent
construction obligations. This module is one focused prerequisite for them.
