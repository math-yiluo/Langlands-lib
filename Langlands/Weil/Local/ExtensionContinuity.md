# Usual-topology continuity along an extension of p-adic fields

Worker 17 authored this module. It imports Worker 17's
`Langlands.Weil.Local.ExtensionParameters` and
`Langlands.Weil.Representation.InductionContinuity`.

Notation is as in `ExtensionParameters`. Fix a prime `p`, p-adic fields `F`
and `E` in independent universes, and an algebra homomorphism
`f : F.Carrier →ₐ[Padic p] E.Carrier`. Write `ι = extensionWeilMap F E f :
W_E → W_F` for Worker 53's actual map of local Weil groups. Continuity here
always means the usual-topology predicate `IsContinuous`. That predicate asks
for continuity of the action into complex endomorphisms with Mathlib's module
topology, and it is not the open-inertia-kernel convention.
`ExtensionParameters` already proves that restriction from `W_F` to `W_E`
keeps continuity on objects (`isContinuous_extensionRestrict`,
`extensionContinuousRestrict`). This module adds the class version of that
statement. It also adds continuity of induction from `W_E` to `W_F`, which
`ExtensionParameters` leaves out of scope.

## Weil representations

- `extensionContinuousRestrictClass` is restriction on genuine isomorphism
  classes of continuous representations, from `F` to `E`. It is the published
  `continuousRestrictClass` along `ι`, which applies because `ι` is
  continuous.
- `isContinuous_extensionInduce` proves that `extensionInduce` keeps
  continuity. `extensionInduce` is the published `induceAlong ι`. Worker 53's
  `extensionWeilMap_isOpenEmbedding` says `ι` is an open embedding, and
  Worker 53's instance `extensionWeilRange_finiteIndex` says its range has
  finite index. With these, the published `isContinuous_induceAlong` applies.
- `extensionContinuousInduce` acts on continuous objects, from
  `LocalContinuousWeilObjects E` in carrier universe `w` to
  `LocalContinuousWeilObjects F` in carrier universe `max u w`, where `u` is
  the universe of `F`. `extensionContinuousInduceClass` is the published
  `continuousInduceAlongClass` along `ι`. It acts on genuine classes with the
  continuity condition, and equivalences come from `induceAlongEquiv`.

## Weil–Deligne pairs

The continuity predicate on pairs is continuity of the underlying
representation (`WeilDeligneRepresentation.IsContinuous`). The underlying
representation of `extensionWDRestrict A` is, by definition,
`extensionRestrict` of that of `A`. The underlying representation of
`extensionWDInduce A` is, by definition, `extensionInduce` of that of `A`. So
`isContinuous_extensionWDRestrict` and `isContinuous_extensionWDInduce` follow
directly from the two statements above. The monodromy plays no role.

## Source correspondence and provenance

Tate, *Number theoretic background*, Corvallis Part II, source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:

- §2, printed page 9 (PDF page 18): a representation of a topological group is
  a continuous homomorphism to `GL(V)` with `V` finite-dimensional complex.
- §2.1, printed pages 9–10 (PDF pages 18–19): restriction
  `res_{E/F} : R(W_F) → R(W_E)` and induction `ind_{E/F} : R(W_E) → R(W_F)`,
  identifying `W_E` with a closed subgroup of finite index in `W_F`.

Tate's maps are between groups built from continuous representations. That
presupposes that restriction and induction keep continuity, but Tate states
no such lemma. This module is derived: it specializes the general results of
`InductionContinuity` to the actual map `ι` and adds no axiom.

## Scope

Only continuity is treated. Irreducibility, Frobenius semisimplicity and
open-inertia conditions are not claimed here to be preserved under induction.
For the open-inertia convention, `ExtensionParameters` gives its own
operations.
