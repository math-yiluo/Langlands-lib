# Four axioms on actual affine scheme point spaces

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, Proposition 2.1 and its proof, printed pages 2–3. Registered
source: `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module states the actual-scheme characterization and the derived
coordinate-algebra transport property. These are proposition-valued targets,
not proofs or assumed fields of a topology structure.

Fix a commutative coefficient ring R and a commutative R-algebra S with a given
topology. R, S and the schemes have a common universe `u`. The indexed schemes
are actual objects of `Over (Spec R)`; their points are actual morphisms from
`Spec S` over that base. `AffineSchemeTopologyFamily R S` is an arbitrary
assignment of a topology to each such point set for affine schemes locally of
finite type over `Spec R`. In this affine setting, local finite type is full
finite type: `affineStructure_quasiCompact` supplies quasi-compactness, and
`affineCoordinate_finiteType_iff` proves equivalence with finite type of the
actual global-section R-algebra.

The source uses the same topological ring as coefficient and value ring.
Specializing S to R recovers that setting. The separate coefficient ring is a
derived relative formulation: polynomial evaluation in S still has constant
coefficients, so no topology on R or continuity assumption on its algebra map
to S is used. The three property targets explicitly retain
`IsTopologicalRing S`; none adds Hausdorffness, locality, noetherianity or finite
presentation.

The four axioms are:

- `AffineSchemeTopologyFunctorial`: every actual relative scheme morphism
  induces a continuous map by postcomposition of points.
- `AffineSchemeTopologyPullbacks`: for every actual limiting relative pullback
  cone on the indexed affine schemes, the projection comparison is a
  homeomorphism to the subtype of pairs with equal composite to the common
  target. The subtype has the subspace topology of the product of the two
  assigned factor topologies. The cone vertex is also required to belong to
  the indexed affine finite-type family; no chosen tensor presentation is part
  of the axiom. Its set bijection comes from the actual limit property in all
  schemes over the base, with no finite-type requirement on `Spec S`.
- `AffineSchemeTopologyClosedImmersions`: every actual scheme closed immersion
  in the indexed family induces a topological embedding. Closed image is not
  imposed; Conrad explains why it requires an additional Hausdorff hypothesis.
- `AffineSchemeTopologyLine`: the actual point-to-coordinate evaluation on
  `Spec (MvPolynomial Unit R)`, a concrete single-variable polynomial affine
  line, is a homeomorphism to S with its given topology. The comparison uses
  `spectrumAlgebraPointEquiv` on actual relative morphisms.

`AffineSchemeTopologyAxioms` is their conjunction. There is no extra finite
product, coproduct or presentation axiom.

`AffineSchemeTopologyExistenceProperty` states that the independently
constructed evaluation family satisfies these axioms.
`AffineSchemeTopologyCharacterizationProperty` states that an arbitrary family
satisfies them if and only if it equals that evaluation family. Equality here is
equality of topology assignments on every indexed actual scheme point set.
These targets cover the first paragraph of Proposition 2.1's existence and
uniqueness assertion, through the actual morphism/global-section construction.
They do not include its additional Hausdorff, closed-image and local-compactness
conclusions or the later examples.

`AffineSchemeTopologyTransportProperty` is a derived bridge to the
coordinate-algebra four-axiom formulation. It states both directions:
algebra families satisfying their axioms transport to scheme families
satisfying the scheme axioms and back to the same algebra family; scheme
families satisfying their axioms transport to algebra families satisfying
the algebra axioms and back to the same scheme family. The transports are the
ones already defined using the actual global-section point equivalence and the
direct spectrum point equivalence. Their inverse property is asserted only
under the corresponding axioms; an arbitrary assignment need not respect
isomorphisms. This module supplies no proof of any of these targets.
