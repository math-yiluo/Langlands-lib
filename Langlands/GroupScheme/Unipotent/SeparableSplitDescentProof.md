# Split unipotence descends along separable field extensions

`Langlands.GroupScheme.separableSplitUnipotentDescent` proves
[`SeparableSplitUnipotentDescentStatement`](SeparableSplitDescentStatement.md)
in every universe. If an affine unipotent algebraic group over a field `k`
admits a split series after a separable algebraic extension `K/k`, it admits
such a series over `k`.

A finite split series on `G_K` identifies its underlying scheme over `K` with
an affine space by `splitUnipotentAffineSpaceStatement`. This gives smoothness
and connectedness, which descend to `G` along the faithfully flat,
quasi-compact map `Spec K ⟶ Spec k`.

The split unipotent radical `N ⟶ G` has a represented smooth affine fppf
quotient `q : G ⟶ Q`. The quotient is connected by surjectivity and unipotent
by descent along the quotient. The central additive-subgroup criterion gives
`HasConstantAffineLineMaps Q` for the quotient by the split radical.
`unipotentWoundSeparableExtension` carries this property to `Q_K`.

Every group homomorphism from an affine group with a split series to a
wound group is zero, so `q_K = 0`. Faithfulness of base change gives `q = 0`.
Consequently its full kernel is all of `G` on every scheme over `k`. The
radical inclusion and the identity of `G` represent the same subgroup
functor, so the isomorphism between their sources transports the split
series of `N` to `G`.

The target is Milne, *Algebraic Groups* (2017), 14.65, printed p.299, registered
as `milne-2017-algebraic-groups`. The affine-space comparison is 14.66 on the
same page. The implemented proof uses the wound quotient argument of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition B.3.2 and Theorem B.3.4, printed pp.572–574, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The Lean inputs for that argument
apply in every characteristic and to the given separable algebraic extension.
