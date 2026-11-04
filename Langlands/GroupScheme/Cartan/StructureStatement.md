# Structure of Cartan subgroups

`Langlands.GroupScheme.CartanStructureStatement.{u}` states the structural
part of J. S. Milne, *Algebraic Groups* (2017), Proposition 17.44,
printed pp.364–365 / PDF pp.380–381, with the Cartan convention of
Definition 17.43 on printed p.364.

For every field `k : Type u` and every actual smooth connected affine
group scheme `G` over `k`, every Cartan embedding `i : C → G` has a source
`C` that is smooth over `k`, connected, and geometrically nilpotent. The
published predicate `IsCartanSubgroup i` requires `i` to be a closed
subgroup embedding whose all-test range equals the centralizer of an
actual maximal torus of `G`. It does not assume the structural conclusions
about `C`.

The conclusion uses `Smooth C.X.hom` and `ConnectedSpace C.X.left`.
Geometric nilpotence is the published predicate
`IsNilpotentGroupScheme C`: the abstract group of points of `C` over the
algebraic closure of `k` is nilpotent. Thus it agrees with the existing
geometric solvability convention for smooth group schemes. The source
`C` is also affine as a closed subgroup of the affine `G`, but the
statement does not include this automatic consequence as an additional
conclusion.

The field may be imperfect and has arbitrary characteristic; it need not
be infinite or algebraically closed. The maximal torus need not be split,
and neither the group nor the torus is required to have positive
dimension. Affineness and smoothness ensure the finite type setting of
the cited algebraic-group result.

Milne proves the three structural conclusions after passage to an
algebraic closure, using smoothness of torus centralizers (13.10),
connectedness (17.38), and nilpotence (17.28). This module records the
proposition as a `Prop`-valued definition; it supplies no proof.
Proposition 17.44 also states conjugacy over an algebraically closed
field and a dense-open union assertion. Those conclusions are outside
this focused statement.

The smoothness part already has a published proof for represented torus
centralizers in `Torus.CentralizerSmoothProof`. Connectedness and
nilpotence remain structural proof obligations here. This statement
provides the Cartan input used in the semisimple-element centralizer
route to Cartan generation; it does not itself prove
`CartanGenerationStatement`.
