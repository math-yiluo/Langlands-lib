# Root Lie spaces of split maximal tori

`Langlands.GroupScheme.SplitRootLieLineStatement.{u}` states that, over every
field `k : Type u`, each root Lie space for a split maximal torus of a connected
reductive group is linearly isomorphic to `k`. This file defines a proposition;
it supplies no proof of that proposition.

The inputs are an actual group scheme `G` over `Spec k`, a proof
`hG : IsConnectedReductive G`, an actual commutative group scheme `T`, a proof
that `T.toGrp` is a split torus, and a homomorphism `i : T.toGrp ⟶ G` exhibiting
it as a maximal torus. Affineness for the Lie construction comes from `hG`.
For every `χ ∈ roots i`, the conclusion is
`Nonempty (k ≃ₗ[k] weightSpace i χ)`.

The imported `weightSpace` is a submodule of the actual Lie algebra defined
using dual-number identity kernels. Its weight equation is tested after every
coefficient-algebra extension and at every point of the torus over that
algebra. The imported `roots i` consists of the nonzero characters whose
weight spaces are nonzero. Thus the conclusion concerns these actual root
spaces. A linear equivalence with `k` expresses freeness of rank one directly
and provides a possible trivialization for choosing a pinning.

The statement specializes the opening field discussion of Conrad,
*Reductive group schemes* (2014), §5.1, printed/PDF p.136. For a connected
reductive group over an arbitrary field with a split maximal torus, that passage
states that every occurring nontrivial Lie weight space is one-dimensional,
hence free of rank one over the field. The source uses geometric
maximality; its opening paragraph also records equivalence with other field
notions of maximality. The imported `IsMaximalTorus` uses factorization through
larger closed tori over `k`. Definition 6.1.1, printed/PDF p.186,
explains how trivializations of the simple-root lines enter a pinning.

The field and the schemes retain arbitrary universe `u`. There is no
perfectness, characteristic or algebraic-closedness hypothesis. The statement
does not construct the torus, a root datum, a base, a full pinning, a pinned
isomorphism, or a quasi-split inner form.
