# Two-cell factorization over arbitrary local rings

Module `Langlands.GroupScheme.Reductive.LocalSplitLocalGeneration`.
The coordinate and factorization helpers are in `Langlands.GroupScheme.LocalSplitCell`.

## Statement

`Langlands.GroupScheme.LocalSplitLocalGenerationStatement.{u}` asserts the following.
Let `R` be any commutative local ring whose residue field is separably closed. Let `G`
be a reductive group scheme over `Spec R` with an affine structure morphism. Let
`i : splitTorus (Spec R) I ⟶ G`, with `I` finite, be a fibrewise maximal torus. Supply
a finite fibrewise root datum `P` on the actual coordinate lattices, a base `b` of `P`,
and actual root parametrizations `fam α : Ga R ⟶ G` for all roots `α`. For any
enumerations `neg` and `pos` of the negative and positive roots, and any actual
`R`-point `g` of `G`, there are `R`-points `x,y` of the coordinate cell such that

```text
g = (x ≫ cellMap i fam neg pos) * (y ≫ cellMap i fam neg pos).
```

Moreover, `g` lies in `Subgroup.closure (generators i fam)`, where the published
`generators` is the union of the images of the actual `R`-points of the torus and
all supplied root maps. The affine typeclass is explicit because it is used by
the fibrewise root-datum interface; reductivity already supplies it.
The theorem `localSplitLocalGeneration` proves this proposition at arbitrary universe `u`.
There is no domain, reducedness, noetherian, Henselian or characteristic assumption.
Separably closed residue field and supplied root parametrizations remain hypotheses.

## Coordinate lifting

`exists_cellPoint_lift` is a more general helper. For any morphism `f : W ⟶ Z`
of test schemes over `Spec R`, assume that pullback of global functions is surjective
and that the induced map on global units is surjective. Every `W`-point of
`cellObj R I m n` then lifts to a `Z`-point. The published
`LocalSplitBigCell.coordTriple_bijective` identifies cell points with a triple:
negative additive coordinates, a split-torus point and positive additive coordinates.
The additive coordinates lift by surjectivity on functions; the torus coordinates
lift by surjectivity on units and `splitTorus.pointsEquiv`. Naturality of these
coordinates shows that restriction of the chosen lift equals the original point.

`exists_cellPoint_lift_residue` applies this to `Spec κ ⟶ Spec R`, where `κ` is
the residue field of a local ring. The residue quotient is surjective, so its
spectrum is a closed immersion and its pullback on global sections is surjective.
The canonical isomorphisms between rings and global sections of their spectra
transport locality and nontriviality. This surjective pullback is therefore a local
ring homomorphism, and `IsLocalRing.surjective_units_map_of_local_ringHom` gives
surjectivity on units. Thus every residue-field point of the cell lifts.
No separable closedness is needed for either coordinate lifting helper.

## Factorization and generation

`exists_two_cell_factors` needs only a reductive `G`, supplied torus and additive
maps, and an open-immersion instance for their cell map. In particular, this helper
does not require a root-datum predicate or assert that the supplied maps parametrize roots.
It proves the same two-cell factorization over a local ring with separably closed
residue field.

The implementation adapts the argument in the published `LocalSplitIntegralGeneration`:

1. Pull back `G` to the residue field. This fibre is smooth, affine and connected.
   The published `baseChangeBasePointsEquiv` identifies its rational points with
   residue-field points of `G` over `Spec R`; restriction of base points preserves
   the group structure.
2. The preimage `U` of the open cell contains the restriction of the coordinate
   cell's unit point. The published field lemma
   `exists_rationalPoint_mem_inv_mul_mem` gives a rational point `q` with both
   `q` and `q⁻¹ * r(g)` in `U`. That lemma uses irreducibility of the smooth connected
   affine group and density of rational points over a separably closed field.
3. Factor `q` through the cell over the residue field using the open immersion.
   Apply `exists_cellPoint_lift_residue` to lift this coordinate point to an
   actual base point `x`; put `h = x ≫ cellMap`. The proof checks the equality
   `r(h) = q` as scheme morphisms.
4. The restriction of `h⁻¹ * g` has its point in the cell. The published
   `exists_lift_of_closedPoint_mem` then factors `h⁻¹ * g = y ≫ cellMap`.
   It applies over every local ring: an open set containing the closed point
   contains every generization. The group identity gives the required product.

`mem_closure_generators_of_open_cell` deduces generation from this factorization
and the published `cellMap_mem_closure`, which expresses each cell point as a
product of supplied torus and additive points.

`exists_two_cell_factors_of_rootParametrizations` obtains the open-immersion
instance from the published `LocalSplitBigCell.isOpenImmersion_cellMap`, whose
base ring is arbitrary. `mem_closure_generators_of_isLocalRing` chooses finite
root enumerations and applies that factorization to obtain generation. The
packaged proposition asserts both conclusions for every supplied enumeration.

## Provenance and scope

This is an internal derived module; it does not quote an external source statement.
Its inputs are the published coordinate model, arbitrary-base big-cell theorem,
separably closed field argument and elementary local-ring lifting of units.
It replaces the Henselian section-lifting step of `LocalSplitIntegralGeneration`
with the explicit coordinate lift above, thereby removing that theorem's
Henselian and domain assumptions.

The module proves generation and factorization, not relations or comparisons
between two groups. It does not construct torus/root-matching point-group
equivalences, and it does not prove `LocalSplitIsomorphismTheoremStatement`.
