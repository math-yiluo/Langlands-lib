# Iterated ordered coordinates and the composite quotient measure

This is an internal coordinate and measure construction motivated by
the literal product and iterated integral in Waldspurger (2003), IV.1,
printed p.279 (PDF p.45), and the composition assertion IV.1(12),
printed p.283 (PDF p.49). It retains geometric and analytic application
obligations.

Given homeomorphisms `a : A × X ≃ₜ J` and `b : J × Y ≃ₜ G`,
`iteratedFactorHomeomorph` is the concrete homeomorphism
`A × (X × Y) ≃ₜ G` sending `(h,(x,y))` to `b(a(h,x),y)`.
It first changes the parentheses and then applies `a` and `b`.
Its inverse first applies `b.symm`, then `a.symm` to the first
coordinate. All five spaces have independent universes.

`measurePreserving_iteratedFactorHomeomorph` assumes that `a` pushes
`μA.prod μX` to `μJ` and `b` pushes `μJ.prod μY` to `μG`.
It proves that the composite pushes `μA.prod (μX.prod μY)` to `μG`.
The three original factor measures are S-finite. The proof uses the
inverse of the measure-preserving product associator, the product of
the first measure-preserving map with the identity, and composition
with the second map. This step has no regularity, Haar or Borel-space
premises.

For the subgroup specialization, `H` and `J` are actual subgroups of a
topological group `G`. The first map has domain `H × X` and codomain
`J`, and the second has domain `J × Y` and codomain `G`. Supply
`s : X → G`, `t : Y → G` and the literal equations
`a(h,x).val = h.val * s(x)` and `b(j,y) = j.val * t(y)`.
Group associativity gives the composite formula
`h.val * (s(x) * t(y))`.

`iteratedFactorQuotientHomeomorph` constructs the actual left-quotient
chart, sending `(x,y)` to `H*(s(x)*t(y))`.
The inverse reads the two successive second coordinates of the
representative. The coordinate spaces `X` and `Y` need only topologies;
neither needs to be a group. No commutation or normality is assumed,
and the construction makes no claim that coordinate multiplication is
a group homomorphism.

For exact quotient normalization, assume that `G` is locally compact
Hausdorff, `H` is closed, and use the displayed Borel structures on
`G`, `H`, `X × Y` and the actual left quotient.
Only measurable structures are required on `J`, `X` and `Y`.
Let `μG` be finite on compact sets and `μH` regular two-sided Haar.
Let `μH`, `μX`, `μY` be S-finite and `μX.prod μY` regular.
For a compatible Weil measure `ν`,
`IsCompatible.measurePreserving_iteratedFactorQuotientHomeomorph`
derives the composite quotient normalization from the two intermediate
product identities and the existing exact product-to-quotient theorem.
No third product identity is an input.

`measurePreserving_factorProduct_of_iterated` also identifies a separately
supplied composite homeomorphism with these constructed coordinates when
its literal product formula agrees. It then derives its ambient product
identity from the same two intermediate identities. It needs only measurable
structures and the three S-finiteness premises in addition to the literal
coordinates. It has no Haar, regularity, local compactness, Borel-space or
topological-group premise.

Applications must provide the two ordered coordinate maps, their literal
equations and their two intermediate measure identities. In a root-distance
application the intermediate subgroup is an intersection subgroup, so its
factorization and Haar comparison remain substantive obligations. Compact-open
normalization can discharge intermediate measure identities where its
hypotheses have been verified. This construction proves neither the general
root product geometry nor convergence or continuation of intertwining
operators, and does not close a whole-program Plancherel condition.
