# Profinite topology on integral Tate limits

This derived construction bundles the published actual integral Tate limit as a
profinite space when its selected torsion-point groups are finite. It preserves
the topology and additive group already defined in `Tate.Integral`.

For an actual commutative group scheme `G/S`, a test scheme `T` over `S`, and a
predicate `P` on natural numbers, the indices are the positive integers satisfying
`P`. Each `Level G T n` is the additive form of the kernel of multiplication by
`n` on actual sections. The existing kernel and fibre equivalences identify these
with points of the actual torsion scheme. The limit consists of families
compatible with the transition maps given by multiplication by the quotient of
indices. Each level has the discrete topology, and the limit has the subspace
topology from their product.

`isClosed_coherent` proves that the compatible families form a closed subset:
each transition equation is an equalizer of continuous maps into a discrete,
hence Hausdorff, level. The full condition is the intersection of these closed
equalizers. The product of discrete spaces is Hausdorff and totally disconnected,
and these properties pass to the subspace without any finiteness hypothesis.
If every selected level is finite, it is compact. Compactness of the product and
closedness of the coherence condition then make the integral Tate group compact.
The implementation uses Mathlib's product compactness and subspace instances.
No surjectivity of the transition maps is needed for this argument.

`continuous_iff_evaluation` gives the induced-product-topology criterion for maps
into the existing limit: continuity is equivalent to continuity at every
coordinate. `profinite` bundles exactly that limit as a Mathlib `Profinite`
object. `profiniteMap` bundles the already constructed homomorphism-induced
continuous map, with its point formula and identity/composition laws. Its
underlying map remains the additive homomorphism from `Tate.Integral`.

The aliases in `Langlands.AbelianScheme.Tate` specialize to actual bundled abelian
schemes. `fullProfinite` selects all positive integers; `awayProfinite p` selects
positive integers coprime to `p`, with no primality assumption needed for this
construction. Each asks for finiteness only at its selected levels. A geometric
point is obtained by taking `T = Over.mk s`, where `s : Spec Ω → S` and `Ω` is
algebraically closed. These are the same types used by `FullAt` and `AwayAt`.

The finiteness hypotheses are explicit. This unit does not prove that an
arbitrary test scheme has finitely many torsion sections, or establish finite
étaleness, rank, or geometric monodromy. When such geometric theorems are used,
their actual hypotheses, including invertibility of torsion orders for finite
étaleness, remain necessary. Rational Tate spaces are not bundled here.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (PDF p.26), defines the full and away-from-primes
Tate limits from actual torsion points. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The arbitrary-predicate/test-scheme construction and the closed-subspace argument
are internal consequences of the published integral definition and standard
product topology, not additional geometric claims attributed to that passage.
The closed-equalizer proof follows the same Mathlib method as the published
compatible-residue scalar-ring construction in `Langlands.Global.ProfiniteIntegerRing`.
