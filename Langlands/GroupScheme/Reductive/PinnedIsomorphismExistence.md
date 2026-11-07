# Chosen actual pinned lifts of based root-datum equivalences

Let `k : Type u` be any field, let `G` and `H` be actual affine group schemes
over `Spec k`, and let `p : SplitPinning G` and `q : SplitPinning H` be supplied
split pinnings. Suppose
`e : RootPairing.Equiv p.rootDatum q.rootDatum` preserves the supports of their
bases: for every source root index `a`,
`a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support`.

`SplitPinning.isoOfRootDatumEquiv p q e hsimple` chooses an actual
`SplitPinning.Iso p q`. This structure contains an actual group-scheme
isomorphism, an actual isomorphism of the supplied tori, their commuting
inclusion square, a root-index equivalence, root and coroot compatibility,
preservation of the simple-root supports, and equality of the supplied
simple-root vectors under the actual linear differential.

The four specification theorems prove the following equalities:

- `isoOfRootDatumEquiv_torusIso` identifies its torus component with
  `p.torusIsoOfRootDatumEquiv q e`.
- `isoOfRootDatumEquiv_indexEquiv` identifies its root-index equivalence with
  `e.indexEquiv`.
- `isoOfRootDatumEquiv_character` identifies its full forward integral
  character-lattice map with `e.weightEquiv`.
- `isoOfRootDatumEquiv_cocharacter` identifies its full forward integral
  cocharacter-lattice map with `e.coweightEquiv.symm`.

The character convention is inverse pullback along the forward torus
isomorphism. Mathlib's coweight equivalence has the opposite direction, which
accounts for the inverse in the cocharacter equation. These are the exact map
equations in `PinnedIsomorphismStatement`.

## Implemented construction and provenance

This is a derived construction from published Library results, with no new
source assertion. `PinnedIsomorphism.exists_iso` in
`Reductive.PinnedIsomorphismReduction` supplies the required existential
witness after its two premises are discharged by
`splitCommonTorusIsomorphism` in `Reductive.SplitIsomorphismProof` and
`pinnedRootScaling` in `Reductive.PinnedRootScalingProof`. The definition uses
classical choice on that existential proposition. Its first two specifications
are the two components of the chosen witness's specification.

The underlying existence proof first lifts the full character-lattice map to
the actual supplied tori using `SplitPinning.torusIsoOfRootDatumEquiv` from
`Reductive.PinningLattice`. It transports the target torus inclusion to the
source torus and applies the common-torus isomorphism theorem. The differential
of that group isomorphism carries each supplied simple-root vector to a
nonzero scalar multiple of the prescribed target vector. Root scaling on the
source by the inverse scalars corrects those vectors while fixing the supplied
torus. The resulting actual pinned isomorphism has the prescribed torus and
index components. The character and cocharacter specifications in this module
follow by rewriting the torus component and applying the corresponding
`torusIsoOfRootDatumEquiv_character` and
`torusIsoOfRootDatumEquiv_cocharacter` theorems.

The construction retains arbitrary `u` and arbitrary fields, the supplied
pinnings, the full integral lattices, central-torus factors and empty root
systems. It imposes no characteristic, perfectness or dimension restriction.
This module proves existence with exact specifications. Uniqueness of the
complete pinned-isomorphism structure, and hence the full
`PinnedIsomorphismStatement`, still requires pinned-automorphism rigidity.
