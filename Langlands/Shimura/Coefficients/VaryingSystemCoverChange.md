# Contravariant cover change of whole varying-torsor systems

Author: Worker 13.

This internal construction makes the associated-sheaf system on varying finite
geometric torsors contravariant in its whole cover diagram. Its inputs and maps
are the actual constructions in [VaryingCoverInverse](VaryingCoverInverse.md),
[VaryingCover](VaryingCover.md), [EtaleCrossCover](EtaleCrossCover.md) and
[CrossCover](CrossCover.md). It introduces no new external-source claim.

Let `X : Scheme.{u}`, let `R : Type u` be a commutative ring, and let
`D : I ⥤ GrpCat.{u}`. The object and morphism universes of the index category
are the independent `uI` and `vI`. Cover diagrams `Y`, `Z`, `W` belong to
`EquivariantDiagram D X.Etale`; a coefficient diagram `M` belongs to
`EquivariantDiagram D (ModuleCat.{u} R)`. Thus the groups can vary with the
index, but a cover-diagram morphism is equivariant for the same group at each
index and is natural in all index arrows. The group diagram `D` remains fixed.
Module carriers, the ring, scheme and groups share universe `u`.

Write `L_Y(M)` for the existing `etaleAssociatedVaryingSystem X Y hY M`.
To form this system, `hY` asserts that each `Y.action i` is a finite geometric
torsor; similarly for `hZ` and `hW`. No filteredness of `I`, surjectivity of
the group transitions, or finiteness, freeness or local-constancy hypothesis
on `M` is added.

For a cover-diagram morphism `a : Y ⟶ Z`,
`etaleAssociatedAtCoverChange X R a i` is the natural transformation
from the `Z_i` associated-sheaf functor to the `Y_i` associated-sheaf functor.
It is obtained by whiskering the existing `etaleAssociatedCoverChange` with
evaluation at `i`. Its component is exactly

`q_a,i(M) = etaleCrossCoverMap X id (a_i) (id M_i)`.

Here the equivariant component `a_i` maps the cover `Y_i` to `Z_i`, so the
associated-sheaf map goes from `Z_i` to `Y_i`. Coefficient naturality comes
from the existing natural transformation, with the full group action retained.
This vertex construction and its identity and composition laws do not require
the torsor hypotheses.

`etaleCrossCoverMap_identity_inclusion` gives the section formula behind the
construction, also for arbitrary group homomorphisms. If `phi : H →* G`,
`a : B ⟶ res(phi) A`, and `M` is a `G`-module action, then

`cross(phi,a,id) ≫ inc_B,res(phi)M = inc_A,M ≫ coverPullback(a,const M.V)`.

The proof expands the existing invariant-lift inclusion formula and removes
the identity coefficient map. The named inclusion is monic.

For an index arrow `b : i ⟶ j`, let `beta_Y,b` be coefficient reduction and
`alpha_Y,b` the contravariant cover-comparison leg of the existing cospan.
Let `q_a,i^b` denote the same pure cover change at `i` with coefficients
`res(D.map b) M_j`. The two square lemmas prove

`q_a,i ≫ beta_Y,b = beta_Z,b ≫ q_a,i^b`,

`q_a,j ≫ alpha_Y,b = alpha_Z,b ≫ q_a,i^b`.

The reduction-square proof composes with the target invariant inclusion,
uses the section formulas, and applies coefficient naturality of
`coverPullback`. The comparison-square proof uses the same inclusions,
contravariant composition of `coverPullback`, and the actual equality
`Y.map b ≫ a_j = a_i ≫ Z.map b` supplied by naturality of `a`.

The existing system transition is
`tau_Y,b = beta_Y,b ≫ alpha_Y,b^(-1)`.
For finite geometric torsors the existing theorem proves `alpha_Y,b`
invertible. Composing with this map, applying the two square lemmas and
using `tau ≫ alpha = beta` proves
`etaleAssociatedTransition_coverChange`:

`tau_Z,b ≫ q_a,j = q_a,i ≫ tau_Y,b`.

Consequently `etaleAssociatedVaryingSystemCoverChange X R hY hZ a` is an
actual natural transformation of functors in coefficient diagrams,
from `L_Z(-)` to `L_Y(-)`. Its component at `M` is a natural transformation
of the entire sheaf diagrams; its component at `i` is exactly `q_a,i(M)`.
The outer naturality is the coefficient naturality of the vertex map.
No desired transition compatibility or chosen comparison is supplied as input.

The vertex identity and composition lemmas prove

`q_id = id`, and `q_b ≫ q_a = q_(a ≫ b)`

for `a : Y ⟶ Z` and `b : Z ⟶ W`. Their proofs use the invariant inclusion
formula and the identity and contravariant composition laws of
`coverPullback`. Extensionality in `M` and `i` gives the corresponding
whole-system laws `etaleAssociatedVaryingSystemCoverChange_id` and
`etaleAssociatedVaryingSystemCoverChange_comp`.

For an actual isomorphism `e : Y ≅ Z`,
`etaleAssociatedVaryingSystemCoverIso X R hY hZ e` is the natural
isomorphism `L_Z(-) ≅ L_Y(-)`. Its forward and inverse maps are cover
change along `e.hom` and `e.inv`. The two inverse laws follow from the
proved composition and identity laws and the inverse laws of `e`.

This unit treats changes of cover diagrams over a fixed scheme and group
diagram. Identity and composition coherence for whole-system base change,
non-etale inverse image, algebraic-closure base change, compact supports,
cohomology comparisons and actual Shimura realization remain separate
obligations. In particular, the torsor hypotheses are inputs to the existing
system construction; this file does not construct Harris's particular torsors.
