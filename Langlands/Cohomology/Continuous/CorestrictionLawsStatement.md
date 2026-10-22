# Continuous corestriction laws

Author: Worker 22. These are exact proposition definitions for the actual
continuous transfer constructed in `Corestriction`. This pair states the laws;
it does not prove them or assume them in the construction.

All five individual propositions quantify over a commutative ring `k` equipped
with a topology, a compact topological group `G`, a module with discrete topology and jointly
continuous action, and every natural degree `q`, including zero. Types have
arbitrary common universe `u`, supporting `ULift.{u} ℤ` as scalars. All map
equalities take place in `ModuleCat k`. The continuous laws use Mathlib's actual
`continuousCohomology`, with its topological structure forgotten. No Hausdorffness or total
disconnectedness hypothesis is added; profinite groups are included.

`FiniteCorestrictionTower` states the corresponding finite-stage tower equation
for `K ≤ H` and an ambient open normal `N ≤ K`. Direct finite transfer from
the quotient of `K` to `G/N` equals the actual `finiteTowerCohomology` map,
finite transfer inside `H` at `restrictOpenNormal H N`, and finite transfer
from `H` to `G` at `N`. The containment proofs in both transfers are derived
from `N ≤ K ≤ H`. Compactness of `H` is locally derived as in the continuous
tower law. This is a separately named helper target for the quotient-image
coordinate argument; the full continuous-law conjunction below asserts the
four continuous laws.

`ContinuousCorestrictionFiniteStage` says that, for every open subgroup `H`
and every ambient open normal subgroup `N` contained in `H`, inflation from
`H/(H ∩ N)` into continuous cohomology followed by continuous corestriction
equals the genuine `finiteCorestriction` followed by ambient continuous
inflation. Fixed coefficients are those of `finiteQuotientRep`; the finite
transfer includes the explicit quotient-image subgroup transport and the
standard-resolution ordinary transfer. This statement records the complete
finite-stage equation, rather than an unspecified compatibility.

`ContinuousCorestrictionNaturality` compares transfer for two discrete modules
`A` and `B` and any morphism `f : A.toTopRep ⟶ B.toTopRep`. The subgroup
coefficient map is the actual restricted `f`. Applying its induced continuous
cohomology map and then transfer equals applying transfer for `A` and then
the ambient continuous cohomology map induced by `f`. These are Mathlib's
`ContinuousCohomology.map` for identity group homomorphisms.

`ContinuousCorestrictionIndex` says that `continuousRestriction`, followed by
continuous corestriction, is `H.toSubgroup.index` times the identity of ambient
continuous cohomology. The imported restriction is the actual
`ContinuousCohomology.map` for subgroup inclusion. The index is finite because
the subgroup is open in a compact group; the natural-number multiple acts on
morphisms of `ModuleCat k`.

`ContinuousCorestrictionTower` says that for open `K ≤ H ≤ G`, direct transfer
from `K` to `G` equals transfer through `H`. The right-hand composite first
uses `continuousTowerCohomologyIso` to identify direct `K` coordinates with
`K.subgroupOf H`, then transfers from `towerOpenSubgroup K H` to `H` and from
`H` to `G`. Its local `CompactSpace H` instance is derived from closedness of
the open subgroup and compactness of `G`; it is not an extra premise. Thus
neither coefficient actions nor subgroup carrier types are silently identified.

`ContinuousCorestrictionCompatibility` groups the finite-stage and naturality
laws; `ContinuousCorestrictionIndexTower` groups the index and tower laws.
`ContinuousCorestrictionLaws` is their conjunction. These named groupings permit
focused exact proof tasks while retaining a single full-law interface.

The provenance is derived from Serre, *Local Fields*, Greenberg translation
(1979), Chapter VII, Section 7, printed page 119 / PDF page 125: corestriction
extends the coset norm to cohomological functors and Proposition 6 is the
index law. Coefficient naturality is part of that functorial extension;
transitivity follows from norm composition and its uniqueness, rather than
being a separately numbered theorem on that page. Chapter X, Section 3,
printed page 154 / PDF page 160 supplies the inflation-indexed fixed-coefficient
limit and the continuous-cochain interpretation. The stated continuous laws
express the corresponding operations after the proved finite-quotient
comparison; the explicit transports and the broader compact-group scope are
formalization choices whose exact equations require independent proofs.

Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
