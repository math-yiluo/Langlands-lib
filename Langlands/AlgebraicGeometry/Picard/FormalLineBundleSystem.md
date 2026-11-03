# Compatible actual line bundles on adic thickenings

This definition specializes the compatible-module systems in the Stacks
Project, Section 30.27, Remark 30.27.2 (Tag 0CYW), to actual locally free
rank-one module sheaves. The retained source is
`stacks-formal-line-bundle-effectivity-2026-11-03`,
`literature/Stacks Project - Grothendieck existence and compatible formal
module systems (2026-11-03)/0CYW.html`. The source uses indices starting
at 1; this module uses natural numbers starting at 0 and exponent `n + 1`.
There is no change to the thickenings or compatibility condition.

For any commutative ring `R : Type u`, ideal `I`, and scheme morphism
`f : X → Spec R`, `FormalLineBundle.adicBase I n` is `Spec (R / I^(n+1))`.
Its projection comes from the actual quotient ring homomorphism. The
transition to the next base thickening comes from the quotient factor
map for `I^(n+2) ⊆ I^(n+1)`. The projection triangle follows from the
quotient-factor equation and contravariance of `Spec`.

`adicSpace f I n` is the chosen scheme fibre product of `f` with this
base projection. `adicProjection` maps it to `X`, and `adicTransition`
is the pullback lift of the identity on the `X` coordinate and the base
transition on the other coordinate. `adicTransition_projection` proves
its projection triangle. All these schemes and arrows are actual
scheme objects and morphisms.

`FormalLineBundleSystem f I` consists of an actual `LineBundle` on
each `adicSpace f I n` and a specified isomorphism from the ordinary
pullback of the next bundle to the current bundle. A line bundle here
is the published full subcategory of module sheaves locally isomorphic
to the structure sheaf. No quotient by isomorphism classes is taken.
There is one transition for each consecutive pair; iterated
transitions are obtained by composition and the ordinary pullback
composition comparisons.

`FormalLineBundleSystem.ofLineBundle f I L` restricts an actual line
bundle `L` on `X` by ordinary pullback along every projection. Its
transition isomorphism is the published `LineBundle.pullbackComp`
followed by the ordinary module pullback comparison for
`adicTransition_projection`, lifted to the line-bundle subcategory.

`FormalLineBundleSystem.Comparison F G` specifies isomorphisms on
every thickening. Its `commutes` field requires the square formed by
the ordinary pullback of the next component and the two transition
isomorphisms to commute. The identity comparison uses identity
isomorphisms. Composition uses componentwise composition; its
compatibility proof uses functoriality of ordinary pullback and the
two supplied commutative squares.

`IsAlgebraization L F` means that there exists such a compatible
comparison from the restriction system of `L` to `F`. Thus arbitrary
unrelated isomorphisms on the individual thickenings do not suffice.
The final lemma supplies the identity comparison for the restriction
system of an actual line bundle.

These are definitions and derived elementary compatibility proofs.
They require neither noetherianness nor completeness nor properness.
They assert no existence theorem for algebraizations and supply no
smooth chart. The rank-one algebraization theorem is a separate
obligation: Stacks Proposition 30.25.4 (Tag 088C) gives coherent
existence under properness and completeness, and further work is
needed to obtain an actual rank-one algebraization.
