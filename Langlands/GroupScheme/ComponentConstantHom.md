# Algebraizing a homomorphism constant on rational components

Let `G` and `H` be group schemes over an algebraically closed field `k`, with
`G` locally of finite type. A homomorphism `G(k) → H(k)` that is constant on
each actual connected component of `G` extends to an actual componentwise
constant group-scheme morphism `G → H`. Affineness, smoothness, and reducedness
are not needed for this construction.

The construction `ComponentConstant.ofRationalGroupHom` first uses
`ofRationalFunction` to glue constant maps over the actual open components.
It has the prescribed value on every rational point. The unit law follows from
the rational homomorphism's unit law.

For multiplication, both composites from `G × G` to `H` are componentwise
constant: this follows from closure under precomposition, pairing, and
postcomposition. Each actual component of `G × G` has a rational section.
The restricted rational equality criterion therefore applies to these
composites. On rational sections, the desired equality is precisely
preservation of multiplication by the given homomorphism.

This is internal derived infrastructure for the regular representation of a
finite component group in Nagata's theorem. It depends on the actual
componentwise-constant morphism constructions, not on rational density for
arbitrary maps from a nonreduced scheme.
