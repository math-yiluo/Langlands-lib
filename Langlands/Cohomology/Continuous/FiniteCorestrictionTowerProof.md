# Finite quotient corestriction transitivity

Authors: Worker 145 (Lean proof and explanation), Worker 22 (the quotient-image
coordinate route supplied with the task).

`Langlands.Continuous.finiteCorestrictionTower` proves exactly the published
`Langlands.Continuous.FiniteCorestrictionTower.{u}`. It applies to every natural
cohomological degree, including zero, in arbitrary common universe `u`. The
commutative ring, compact topological group, jointly continuous discrete module,
open subgroups `K ≤ H`, and open normal subgroup `N ≤ K` are precisely those of
the target. Compactness and the topological group structure of `H` are derived
locally. There are no additional hypotheses.

The maps are the published `finiteCorestriction` and `finiteTowerCohomology`,
with their actual fixed coefficient representations. The ordinary transfer is
`Tate.ordinaryCohomologyCorestriction`, constructed from the standard resolution.
The theorem does not change these maps or assume a finite or continuous tower
law. The final unapplied example checks the full target at universe `u`.

## Quotient coordinates

Write `Q = G/N`, `Kbar = image(K → Q)`, `Hbar = image(H → Q)`,
`Hq = H/(N ∩ H)`, `J = image(K.subgroupOf H → Hq)`, and
`L = Kbar.subgroupOf Hbar`. The explicit published equivalence
`quotientSubgroupEquiv H N : Hq ≃* Hbar` is denoted by `e`.
The representation on `Q` is `Aq = A.toRep.quotientToInvariants N`.

The helpers in namespace `FiniteTower` are internal transport certificates:

- `image_mem_iff` proves that `J` is the inverse image of `L` under `e`.
  On a representative `g ∈ H`, forward membership follows by applying the
  quotient inclusion to a witness. Conversely, a witness `y ∈ K` with
  `[y] = [g]` gives `y⁻¹g ∈ N ≤ K`, hence `g ∈ K`.
- `imageMap` restricts `e` to a homomorphism `J → L`. Its composite with the
  inclusion of `L` is the restriction of `e` by construction.
- `imageCoefficient` is `fixedRestrictionEquiv A H N` on underlying vectors,
  restricted to `J`. Its equivariance follows from `quotientRestrictionIso`.
  In particular its underlying linear map is exactly that of the ambient
  coefficient map; this is the compatibility required by transfer covariance.

## Two commuting diagrams

Let `I_K`, `I_H`, and `I_J` be the published
`quotientSubgroupCohomologyIso` for `(K,N)`, `(H,N)`, and
`(K.subgroupOf H, N ∩ H)`. Let `U` be the ordinary cohomology tower
coordinate map for `Kbar ≤ Hbar`, and let `P` be the cohomology map induced by
`imageMap` and `imageCoefficient`. Write `T_L` and `T_J` for the ordinary
transfers out of `L` and `J` respectively. Composition below uses Lean's
left-to-right notation `≫`.

`transfer_square` proves

```
T_L ≫ I_H.inv = P ≫ T_J.
```

It applies the published
`ordinaryCohomologyCorestriction_comp_map` with the surjective group map `e`,
the inverse-image subgroups just identified, and the compatible coefficient
maps. Before applying covariance, it identifies `I_H.inv` with the cohomology
map for `e` and `quotientRestrictionIso.hom` using `mapIso_inv` and
`map_congr`. This argument works in every natural degree.

`coordinate_square` proves

```
I_K.inv ≫ F = U ≫ P ≫ I_J.inv,
```

where `F` is `groupCohomology.map` for `towerQuotientHom` and
`towerFixedCoefficient`. This is definitionally the target's
`finiteTowerCohomology`. Expanding the inverse cohomology isomorphisms and
combining consecutive maps with `groupCohomology.map_comp` reduces the equality
to `map_congr`. The group homomorphisms agree on quotient representatives;
the coefficient linear maps agree definitionally, retaining the underlying
fixed vectors.

## Assembly

The main proof obtains finite instances from openness and compactness for `Q`
and `Hq`, then for the relevant subgroups and coset spaces. Cancelling the
isomorphisms in the two displayed identities gives

```
I_K.hom ≫ U ≫ P = finiteTowerCohomology A h N q ≫ I_J.hom,
T_L = P ≫ T_J ≫ I_H.hom.
```

The published `ordinaryTransferLaws.2`, due to Workers 25 and 259, states
`T_Kbar = U ≫ T_L ≫ T_Hbar`. Substituting the two identities, associating the
composites, and unfolding `finiteCorestriction` and `quotientCorestriction`
proves the exact target. All containments in the result are the target's
specified consequences of `N ≤ K ≤ H`. General covariance is imported from
Worker 222's published `CorestrictionInflation`; these published dependencies
are used unchanged.

## Provenance

The mathematical provenance is Serre, *Local Fields*, Greenberg translation
(1979), Chapter VII, Section 7, printed page 119 / PDF page 125: corestriction
extends the coset norm to the cohomological functors. Tower transitivity follows
from composition of norms and uniqueness of the extension; it is not a
separately numbered assertion on that page. Chapter X, Section 3, printed page
154 / PDF page 160 describes the fixed-coefficient finite quotient system and
its relation to continuous cohomology. Those pages were read for this proof.

The implemented proof instead reuses the established ordinary tower law and
general covariance, adding the explicit quotient-coordinate certificates
above. These certificates are internal consequences of the Library's actual
definitions. Continuous descent is outside this theorem's scope.

Literature ID: `serre-1979-local-fields`. Retained source:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
