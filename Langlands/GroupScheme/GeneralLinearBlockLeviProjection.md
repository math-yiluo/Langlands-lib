# Coarser block Levi projections on block unipotent subgroups of `GL_n`

This internal module compares two weights `e w : n → ℤ` on a finite index type,
under the hypothesis `hw : ∀ i j, e i ≤ e j → w i ≤ w j`. Then `w i` depends only
on `e i`, weakly increasingly, so the `w`-blocks are unions of `e`-blocks. All
subgroups are the existing `blockUnipotentSubgroup`, `blockParabolicSubgroup`
and `blockLeviSubgroup` of `Langlands.GroupScheme.Dynamic.GeneralLinear`. Here
`blockUnipotentSubgroup A v` consists of the invertible matrices `g` with
`g i j = δ i j` whenever `v i ≤ v j`.

## Matrices

For a commutative ring `A`, `blockUnipotentSubgroup_le_of_le` proves that the
`w`-block unipotent subgroup lies in the `e`-block unipotent subgroup.
`blockUnipotentSubgroup_le_blockParabolicSubgroup_of_le` proves that the
`e`-block unipotent subgroup lies in the `w`-block parabolic subgroup: when
`w i < w j`, `hw` gives `e i < e j`, so the entry `g i j` is zero.

`blockLeviProjection_mem_of_le` shows that the existing `w`-block Levi projection of
an `e`-block unipotent matrix is again `e`-block unipotent and is `w`-block
diagonal. Its block diagonal part keeps the entries with `w i = w j` and
sets the others to zero. `unipotentLeviProjection A hw`
is the resulting group homomorphism from `blockUnipotentSubgroup A e` to
`blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w`. Its underlying matrix is
`blockDiagonalPart A w g` (`coe_unipotentLeviProjection`).

The projection has three properties:

- `unipotentLeviProjection_of_mem`: it fixes every element of the intersection
  `blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w`.
- `unipotentLeviProjection_eq_one_iff`: its kernel is exactly the `w`-block
  unipotent subgroup.
- `map_unipotentLeviProjection`: it commutes with every coefficient ring
  homomorphism `A →+* B`.

For a topological ring `A`, `continuous_blockDiagonalPart` proves that taking
a block diagonal part is continuous on matrices with the product topology.
`continuous_unipotentLeviProjection` then proves the projection continuous for
the subspace topology of the units topology on `GL n A`.

## Points of the subgroup functors

Fix a commutative ring `R` and an `R`-algebra `S`. `GL_n` over `R` is the
existing `groupScheme n R`, and the affine points over `S` are its morphisms
from `(algSpec R).obj (op S)`. `affinePointsEquiv n R S` identifies them with
`GL n S`.

`mem_ofMatrixSubgroups_affinePoints_iff` states that, for a subgroup functor
built by `ofMatrixSubgroups` from a coefficient-stable family `H`, an affine
point lies in it iff its matrix lies in `H (CommRingCat.of S)`. The proof
transports membership along the global-sections isomorphism
`Corepresented.affineSectionsIso S` in both directions.
`ofMatrixSubgroupsAffineEquiv` is the resulting group isomorphism between these
affine points and `H (CommRingCat.of S)`. The two `simp` lemmas record its
underlying matrices.

`leviUnipotent n R e w` is the subgroup functor of points that are `e`-block
unipotent and `w`-block diagonal. `mem_leviUnipotent` unfolds its membership,
and `leviUnipotent_le` places it inside `blockUnipotent n R e`.
`blockUnipotentAffineEquiv` and `leviUnipotentAffineEquiv` are the
specializations of `ofMatrixSubgroupsAffineEquiv` to `blockUnipotent n R e` and
`leviUnipotent n R e w`, with the matrix families given explicitly.
`blockUnipotent_le_of_le` is the subgroup functor version of
`blockUnipotentSubgroup_le_of_le`.

`pointsLeviProjection R hw S` transports `unipotentLeviProjection S hw`
through these two isomorphisms. It is a group homomorphism from the affine
points of `blockUnipotent n R e` over `S` to those of `leviUnipotent n R e w`.
Its properties:

- `affinePointsEquiv_pointsLeviProjection`: its matrix is the matrix
  projection of the matrix of the point.
- `pointsLeviProjection_inclusion`: it is a retraction of the inclusion
  of `leviUnipotent n R e w` into `blockUnipotent n R e`.
- `pointsLeviProjection_eq_one_iff`: a point lies in its kernel iff the point
  lies in `blockUnipotent n R w`.
- `pointsLeviProjection_naturality`: it commutes with composition along
  `(algSpec R).map g.op` for every `R`-algebra map `g : S ⟶ S'`. The proof
  uses `affinePointsEquiv_naturality` and `map_unipotentLeviProjection`.
- `continuous_pointsLeviProjection`: for a topological ring `S`, it is
  continuous for the topologies induced by the published point topology.
  The proof uses the continuity of `affinePointsEquiv n R S` and of its
  inverse.

Together these give the semidirect decomposition of the `e`-block unipotent
points into the normal `w`-block unipotent points and the complement
`leviUnipotent n R e w`. The module states the decomposition only through the
retraction, kernel and continuity lemmas above.

## Provenance

The module is internal. Its content is elementary block matrix algebra, with
the published block subgroups, affine point equivalences, their naturality and
their topologies. No literature theorem is invoked. The module constructs no
quotient or measure and makes no claim about rational parabolic subgroups.
