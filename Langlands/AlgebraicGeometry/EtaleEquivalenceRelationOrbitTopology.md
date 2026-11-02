# Minimal closed invariant subsets with finite orbits

Authors: Worker 101 and Worker 239.

This internal topological construction isolates part of the proposed
nonzero-invariant argument for the Serre criterion. It does not construct
the point equivalence relation of a scheme relation, prove finite fibers,
or prove the nonzero-invariant theorem.

For a topological space `X` with a `Setoid X`, `Invariant S` means that
`S` is a union of equivalence classes. The construction
`minimalClosedInvariant S hS` chooses a minimal nonempty closed invariant
subset of any supplied nonempty closed invariant subset `S`, when `X` is
Noetherian. It uses the well-founded strict inclusion order on the closed
subsets. Its specification includes containment in `S`.

If `X` is T₀, all classes are finite, and closure preserves invariance,
`eq_class_of_minimal_closed_invariant` proves that every minimal nonempty
closed invariant subset is exactly the class of each of its points.
Consequently it is finite, as is the chosen `minimalClosedInvariant`.

The implemented argument uses finite closures rather than generic-point
existence. A nonempty finite subset `A` contains a point `g` whose singleton
closure is maximal among singleton closures of points of `A`. If another
finite subset `B` has the same closure, then some `b` in `B` specializes to
`g`, and some `a` in `A` specializes to `b`. Maximality makes `g`
specialize to `a`, hence to `b`. T₀ separation gives `g = b`, so `g`
belongs to every such `B`. In a minimal closed invariant subset, closure
of each class is the whole subset. The common point therefore belongs to
all classes, making them one class.

The auxiliary `invariant_closure_of_open_maps` verifies closure invariance
when a pair of continuous open maps `s, t : R → X` presents the equivalence
relation on points. The preimages of an invariant subset along `s` and `t`
agree. For continuous open maps, taking preimages commutes with closure,
so those preimages also agree for its closure.

Worker 239 supplied the host finite-orbit strategy; Worker 101 supplied the
finite-closure refinement and its implementation. All results here are
internal and use only Mathlib topology and finite-order results. In
particular, finiteness here does not prove that these points are closed in
the resulting subspace. Constructing a restricted reduced étale relation
and proving discreteness or the required closed-point property remain
separate obligations.
