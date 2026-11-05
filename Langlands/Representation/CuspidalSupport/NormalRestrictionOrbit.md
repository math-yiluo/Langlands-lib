# A single orbit of simple normal-subgroup types

This derived helper module proves the pairwise single-orbit part of Renard
VI.3.2(i) for any normal subgroup of a group, assuming irreducibility of the
ambient representation and of the two supplied subrepresentations. It does not
assert constituent existence. The main construction
`equivOfAsSubmoduleEquiv` transports an equivalence of ambient group-algebra
submodules back to an equivalence of their original subrepresentations; the
other declarations implement its single-orbit application. Group and carrier
universes are independent.

`translates_span` works over any field. Given a simple subrepresentation `W`,
choose a nonzero vector in it using
`FiniteIndexRestriction.exists_ne_zero`. The published
`FiniteIndexRestriction.span_orbit_eq_top` says that the orbit of its underlying
nonzero ambient vector spans the whole irreducible representation. Every orbit
vector `ρ(g)v` belongs to `FiniteIndexRestriction.translate ρ H g⁻¹ W`, since
applying `ρ(g⁻¹)` gives `v`. Thus the sum of these translates contains the
whole carrier. `translates_asSubmodule_span` transports this equality to the
submodules of the group-algebra module through
`Subrepresentation.subrepresentationSubmoduleOrderIso`. This proof implements
the usual invariant-sum argument through the existing orbit-span lemma.

`equivOfAsSubmoduleEquiv` composes the module equivalences of
the imported `subrepresentationAsModuleEquiv` (declared in the namespace
`Langlands.NormalRestrictionOrbit`) on its source and target with the
given group-algebra linear equivalence. Mathlib's
`Representation.IntertwiningMap.equivLinearMapAsModule` turns its linear map
into an intertwiner, and bijectivity gives a representation equivalence. Every
map retains the original subrepresentation carrier and action.

For `singleOrbit`, take the set of all translated submodules of `W₁`.
The imported covariance helper's `isIrreducible_translate` and its
irreducibility–simple-module bridge show that every member of this set is
simple. The spanning identity above gives its supremum as the whole module.
Apply Mathlib's
`Submodule.linearEquiv_of_sSup_eq_top` from
`Mathlib.RingTheory.SimpleModule.Isotypic` to `W₂`: a simple submodule in a sum
of simple submodules is isomorphic to one of the summands. Reverse that
equivalence, turn it into a representation equivalence, and compose with
`translateEquiv ρ H g W₁`. This yields an equivalence from the action
`h ↦ σ₁(g⁻¹hg)` to the action on `W₂`, exactly the inverse-conjugation
direction of the target. The topological-group hypotheses and complex scalars
match the existing inverse-conjugation API; no representation smoothness,
finite-dimensionality, finite-index or finiteness hypothesis is used here.

The source motivation is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, VI.3.1(ii) and VI.3.2(i),
printed pp.142–144 / PDF pp.148–150, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source proves that the nonzero isotypic components form one orbit, using
the irreducibility of the ambient representation and the preceding
semisimplicity result. The present proof isolates the pairwise assertion and
generalizes it to arbitrary normal subgroups once the two simple
subrepresentations have been supplied. Its elementary module bridges are
internal proof constructions. It proves neither the existence of a simple
subrepresentation nor Renard VI.3.2(ii), finite orbit size or a downstream
inertia decomposition.
