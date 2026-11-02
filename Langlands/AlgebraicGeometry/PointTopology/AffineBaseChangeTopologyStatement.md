# Topology comparison under actual affine base change

Author: Worker 208.

`AffineBaseChangeTopologyStatement` states that, for every compatible
commutative algebra tower `C → D → A`, every topological ring `A`, and every
actual affine scheme `X` over `Spec C`, the existing function
`ringPointBaseChangeEquiv C D A X` is a homeomorphism.

The source is the actual set of morphisms `Spec A → X` over `Spec C`.
The target is the actual set of morphisms `Spec A → X ×[Spec C] Spec D`
over `Spec D`. Each side has its independently defined evaluation topology,
using that affine scheme's own actual global-section algebra. The target
topology is not defined by transport along the base-change equivalence.
The map is the existing pullback-adjunction equivalence: its inverse
composes with the first pullback projection.

This is a derived general comparison underlying the local affine point
spaces used in Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed page 6, the local base-change notation
preceding Theorem 3.6 and (3.6.1). Proposition 2.1 on printed page 2 describes
the affine topology by all coordinate-algebra evaluations. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The statement retains an arbitrary common universe `u` for the rings and
schemes. It assumes no topology on either base ring `C` or `D`, no
continuity of their algebra maps, and no finite-type, local-ring, open-unit,
Hausdorff or separation hypothesis. Its topological-ring assumption is on
the value ring `A`. This generality concerns the existing evaluation
topology, extending beyond the finite-type scope of Conrad's Proposition
2.1. The tensor-coordinate construction supplies a route to the comparison;
the statement specifically requires the original scheme-point function.

This file states the comparison and contains no proof. The arithmetic local
and adelic rings, their model base changes, and nonaffine point topologies
remain separate obligations.
