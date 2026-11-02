# Compactness of actual points over compact value rings

This is a derived prerequisite for the compactness of integral points in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, Corollary 3.7 and its proof, printed page 9, and
Corollary 5.7 and its proof, printed pages 16–17. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This pair states the compact-value-ring prerequisite and supplies no proof.
All three named properties explicitly bind `IsTopologicalRing S`, `T2Space S`
and `CompactSpace S`; these assumptions are retained in their exported types.

The base ring `R` and value algebra `S` are arbitrary commutative rings in a
common arbitrary universe. Only `S` is topologized; it is a compact Hausdorff
topological ring. `AffineSchemeCompactnessProperty R S` says that every actual
finite-type affine relative scheme has a compact space of actual `S`-points,
with its existing global-section evaluation topology. Affineness and local
finite type of the structure morphism give precisely the required finite-type
coordinate algebra. There is no local-ring assumption in this assertion.

`SchemePointCompactnessProperty R S` adds that `S` is local. For every actual
relative scheme whose structure morphism is locally of finite type and whose
underlying scheme space is compact, it asserts compactness of its actual
`S`-points with the published `schemePointTopology`. Compactness of the
underlying scheme space is the usual scheme quasi-compactness condition.
Over the affine base `Spec R`, these scheme hypotheses have the usual
finite-type meaning. No separatedness or quasi-separatedness is required.
`CompactValueRingPointProperties` conjoins the affine result with this
separately local consequence.

The general compact-value-ring formulation is derived rather than a verbatim
theorem from the paper. Its affine argument is the finite-coordinate closed
embedding used in Proposition 2.1: the point space is a closed subspace of a
finite power of `S`, hence compact. A quasi-compact scheme has a finite affine
open cover. Locality of `S` makes the induced affine-chart maps cover all
actual points, and each such map is continuous by the definition of the final
topology. A finite union of their compact images is compact. This isolated
argument needs neither open units nor continuous inversion. It asserts no
open-embedding property for charts under these weaker hypotheses.

These statements do not identify the valuation ring of a locally compact
field with a compact value ring, construct algebraic-space integral-point
topologies, or compare integral and fraction-field points. The image,
injectivity and open/closed-image issues in Corollary 5.7, particularly for
nonseparated models, remain separate obligations.
