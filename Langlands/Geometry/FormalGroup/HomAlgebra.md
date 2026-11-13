# Addition and composition of formal homomorphisms

For finite-coordinate commutative formal group laws `G` and `H` over a
commutative ring `R`, `Hom G H` is an additive commutative group. The sum
of `f` and `g` is the actual pointed map `H.addition.comp (f.pair g)`;
negation composes with `H.inverse`, and zero is the zero series map.
These are formal addition and inverse operations, not coefficientwise
addition and negation of power series.

`CoordinateMap.ext_eval` detects formal-map equality by evaluation at the
tuple of variables. `Hom.ofPointAdditive` uses this to recover the formal
homomorphism identity from additivity on all series-point groups.
The addition and inverse above preserve this identity because evaluation
turns them into pointwise operations in an additive commutative group.
Evaluation is additive in the homomorphism (`onPointsAddHom`).
Composition distributes over addition in both arguments and preserves zero.
Consequently `Hom G G` is a ring, with multiplication `g * f = g.comp f`.
Coefficient change preserves zero, addition, identity and composition;
`Hom.mapEnd` packages it as a ring homomorphism between formal
endomorphism rings.

This is derived infrastructure for formal module actions and rational
homomorphisms. Drinfeld, *Coverings of p-adic Symmetric Regions* (1976),
§1, printed p.108, defines the O-action on the underlying formal group;
§2 A, printed p.109, uses `Hom(X,Y) ⊗_O K` for quasi-isogenies. The
particular coordinate API and the generic-point proof method here are
internal implementation choices. This module does not yet construct
O-actions, O-linear Hom, rationalization, quasi-isogenies, heights or the
locally glued formal groups allowed at the end of §1 on p.109.
