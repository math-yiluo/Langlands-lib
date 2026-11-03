# Open stages of the actual point colimit

This target isolates the topological direct-limit assertion in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (31 December 2011), printed
page 9, section 4, first paragraph. That paragraph explicitly permits open
continuous transitions which are not injective, and gives their actual images
the quotient topologies from the stages. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The original page was read for this target. No registered errata file was
present at the workspace's Library base.

`FilteredRingPointOpenStages` is a proposition; this file supplies no proof.
It quantifies over any commutative ring `R`, any small filtered category `J`,
any diagram `F` of commutative `R`-algebras, any scheme `X` over `Spec R`,
and independently specified topologies `τ j` on the actual stage point sets.
All these data are in one arbitrary universe. The carriers, transition maps,
type-colimit quotient, final topology and quotient-topologized actual stage
images are those of `FilteredRingPoints` and `FilteredRingPointTopology`.
In particular, a transition sends `p` to `p.changeRing (F.map f).hom`.

Assume that every such transition is continuous and open with respect to
the specified source and target stage topologies. The target asserts:

1. Every canonical stage map `ringPointColimitι` into the final-topologized
   actual point colimit is open.
2. The inclusion of each actual stage image, with its already defined
   quotient topology, is an open embedding into that colimit. Thus this
   quotient topology agrees with the subspace topology and the image is
   open. No injectivity assumption occurs in either of these conclusions.
3. If every transition is additionally injective, every canonical stage
   map itself is an open embedding.

This is a derived application of the source's general topological assertion
to the actual fixed-model point diagram, extended from directed index sets to
small filtered categories. The extension uses the filtered type-colimit
equality criterion: two representatives agree precisely when their images
agree after maps to a common later object. For an open set at one stage,
the preimage of its colimit image at another stage is a union of inverse
images of transition images of that open set. This explains why both
continuity and openness are retained and why injectivity is unnecessary
for the first two conclusions. In the injective case the same-stage
filtered equality criterion gives injectivity of each stage map.

There is no finiteness, affineness, separation, locality, Noetherianity,
arithmetic, or algebra-colimit hypothesis here. This target does not assert
that arbitrary algebra transitions induce continuous or open point maps.
It does not identify the point colimit with points over a cocone algebra;
that uses a separate finite-presentation comparison. It also does not supply
actual arithmetic stage topologies, compare varying models, prove model
independence, or establish local compactness or Hausdorffness of adelic points.

In the adelic application, the stage topologies must be the global product
topologies of Theorem 3.6, printed pages 6–8. The top of printed page 9
explains why affine-open gluing does not construct those stage topologies
for nonaffine schemes. Instantiating those topologies and proving their
transition properties remain obligations of the parent development.
