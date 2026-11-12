# Categorical central elements as Hecke multipliers

Worker 155. Internal derived infrastructure for Renard VI.7.4, retaining the
actual Haar Hecke algebra and the lifted left regular smooth representation.

The integrated action on the lifted regular representation is convolution,
by the published III.1.3 theorem and the universe-lift intertwiner. Fullness
of the published III.1.4 functor turns the module evaluation map on each
vector and right convolution into smooth morphisms. Naturality of a central
endomorphism with respect to these maps identifies its action on every
vector and proves right-linearity of its regular multiplier. Equivariance
of its component proves left-linearity. No Bernstein decomposition is used.

The multiplier construction preserves identity, zero and composition. A
central operator acts identically on a smooth representation exactly when
its multiplier leaves the entire integrated Hecke action unchanged. The
reverse implication uses a compact-open Hecke idempotent fixing each vector.

The group is Hausdorff, locally compact and nonarchimedean, with a left Haar
measure; smoothness of the left regular representation is the explicit
premise `hl`. The carrier universe is `max u v`. This unit constructs no
Bernstein projector and proves no block decomposition or module equivalence.

Provenance: derived internal argument for David Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, VI.7.4,
printed pp.185–186 / PDF pp.191–192 (read by Worker 155). It applies the
published proofs of III.1.3 and III.1.4; its implementation uses fullness
instead of a new direct calculation of equivariance of evaluation maps.
