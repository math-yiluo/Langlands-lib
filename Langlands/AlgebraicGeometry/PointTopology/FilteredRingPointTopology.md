# Final topologies on actual scheme-point colimits

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (31 December 2011), printed page 9, section 4,
the two paragraphs defining the topology on a directed set-colimit and
describing its stage images. The fixed-model point map to which this is
applied is on printed pages 5–6, Remark 3.5 and (3.5.1).
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Let `R` be any commutative ring, `J` any small category, `F` a diagram
of commutative `R`-algebras, and `X` any scheme over `Spec R`.
These data are in one arbitrary universe `u`. Specify a topology `τ j`
on each actual point set `RingPoint R X (F.obj j)`.
Neither filteredness nor continuity or injectivity of the transition
maps is needed to construct the following topologies.

`ringPointColimitTopology` is the supremum of the topologies coinduced
by the canonical stage maps `ringPointColimitι` to the actual type-colimit
quotient `RingPointColimit`. Thus a subset is open exactly when its
inverse image at every stage is open. The stage maps are continuous,
and a function out of the quotient is continuous exactly when all of
its stage restrictions are continuous. The codomain of this last
property can have any independent universe `v`.
These are intrinsic final-topology laws, proved with Mathlib's
supremum and coinduced-topology formulas.

For any algebra cocone `c`, `ringPointCoconeTopology` independently takes
the supremum of the topologies coinduced by the actual change-of-algebra
maps from the stages to `RingPoint R X c.pt`. Its open sets and continuous
maps have the corresponding stagewise characterizations.
It is defined directly on these actual relative scheme points and does
not use an inverse to the colimit comparison.

`ringPointColimitMap_coinduced` proves that coinducing the first final
topology along the existing canonical comparison gives the second.
The proof distributes coinduction over the supremum and uses the
comparison's defining stage formula. Consequently the comparison is
continuous; if it is surjective it is a quotient map.
`ringPointColimitHomeomorph` upgrades an independently supplied proof
of bijectivity to a homeomorphism between these two specified final
topologies. Its underlying function is exactly `ringPointColimitMap`.
No bijectivity, finite-presentation theorem or algebra-colimit witness
is assumed or proved by the topology definitions themselves.

`RingPointColimitStageImage` is the actual set-theoretic range of a stage
map. `ringPointColimitStageProjection` is that map with codomain restricted
to its range. `ringPointColimitStageImageTopology` is coinduced from the
stage along this surjection, which is therefore a quotient map.
No injectivity is imposed. This is the quotient topology on the stage
images used in Conrad's nonseparated discussion. Agreement with the
subspace topology and openness of those images require additional
transition hypotheses and are separate results.

The construction generalizes the source's directed system to an arbitrary
small algebra diagram only for these defining final-topology laws.
It imposes no affineness, finiteness, locality, separation, Noetherianity,
or arithmetic condition on `X`, `R`, or the value algebras.
It does not prove openness or continuity of transitions, the
finite-presentation comparison, a comparison of varying models, model
independence, or any adelic local compactness, Hausdorffness or product
property.

For the adelic application the specified stage topologies must be the
global product topologies of Theorem 3.6, printed pages 6–8.
As Conrad explains at the top of printed page 9, affine-open gluing does
not construct these stage topologies for nonaffine schemes.
Instantiating them on the actual arithmetic level rings, proving the
needed transition properties, and comparing varying models remain
obligations of the parent development.
