# Krull continuity of the coefficient action on actual components

Author: Worker 1107.

`ComponentGaloisKrullContinuityStatement` is a proposition target for the
published coefficient action on actual connected components. It is a derived
statement over `ComponentGaloisImage`; this module supplies no proof of the
target and cites no external structural theorem.

The statement quantifies fields `k` and `L` in the same arbitrary universe,
an algebra structure `k → L`, algebraic closedness of `L`, algebraicity of
`L/k`, and a smooth affine group scheme `H` over `Spec k`. The base field
need not be perfect, and there is no characteristic restriction. These
hypotheses are explicit; no rational representatives, splitting field or
openness premise are supplied as inputs.

For every such group and extension, the target asserts all four conclusions:

1. There exists an actual intermediate field `E` of `L/k`, finite dimensional
   over `k`, whose fixing subgroup in `Aut_k(L)` is contained in the published
   `componentGaloisKernel k L H`.
2. That kernel is open in Mathlib's Krull topology on `Aut_k(L)`.
3. The canonical `componentGaloisProjection k L H` is continuous into the
   published finite effective image with its discrete topology.
4. The map `(σ, c) ↦ allComponentGaloisAction k L H σ c` is jointly continuous
   on the product of the Krull automorphism group and the full actual component
   space of `H_L`.

The component space in the fourth conclusion is the published
`AlgebraicallyClosedComponents (baseChanged k L H)`: its carrier consists of
all connected components of the actual underlying scheme. Its topology is
the inherited connected-component quotient topology, proved discrete in
`ComponentGaloisImage` under these hypotheses. The action is the existing
coefficient action, already compared with the actual semilinear scheme maps.
Thus the final assertion concerns that actual action and topology.

The derived provenance is the proposed finite-coordinate route over these
published constructions. There are finitely many actual components and a chosen
actual rational section in each. Smoothness and affineness supply a finite type
affine coordinate algebra. Algebraicity of `L/k` permits a finite intermediate
field containing the evaluations of finitely many algebra generators at these
finitely many sections. Its fixing subgroup should fix each section and hence
every component. Mathlib's Krull neighbourhoods then give the proposed openness
and continuity conclusions. This explains the target's design; none of those
steps is proved in this statement module.

The witness `E/k` is only required to be finite. The statement does not assert
that it is separable or Galois, identify the finite image with `Gal(E/k)`, or
construct a component group scheme or a sheaf quotient. Generalization to
nonalgebraic `L/k` and descent of fixed components to rational points remain
separate obligations.
