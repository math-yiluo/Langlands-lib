# Statement: affine étale split maximal-torus charts for a relative parabolic

Worker 597.

`Langlands.GroupScheme.RelativeParabolicSplitMaximalTorusChartStatement.{u}` is a
`Prop`-valued statement definition. No proof or new axiom is supplied.

For every scheme `S`, reductive group scheme `G` over `S`, relative parabolic
`i : P ⟶ G`, and point `s : S`, the statement asks for a commutative ring `r`, an
étale map `f : Spec r ⟶ S`, and a point `t : Spec r` with `f(t) = s`. On this chart
there must be a finite index type `I` and a closed inclusion
`j : Gₘ^I ⟶ P_f`. For every point `x` of `Spec r`, the composite from `Gₘ^I` to
`G_f`, after base change to the chosen algebraic closure of `κ(x)`, must satisfy
`IsMaximalTorus`.

The standard split-torus base-change isomorphism identifies the domain of each
geometric-fibre map with the standard split torus over that algebraically closed
field. The maximality condition concerns the composite into `G_f`. Closedness of
`j` concerns the inclusion into `P_f`. The map `f` is not required to be globally
surjective; its image contains the specified point `s`. No identification of the
residue fields at `t` and `s` is required.

## Source and derivation

Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
All pages below are one-based PDF pages, equal to the printed page numbers.

Proposition 5.2.3, p.152, asserts that a relative parabolic in a reductive group
contains a maximal torus of the ambient group étale-locally. Its proof first
applies Theorem 3.2.6, p.94, to the parabolic itself and observes that its maximal
torus is also maximal in the ambient group. It then splits the torus by a further
étale localization. The chart statement isolates this part of the proposition.
It does not assert the proposition's global closedness or cocharacter conclusions.

After splitting, choose an affine open neighbourhood of a point lying above `s`
and identify the split torus with a finite product of multiplicative groups.
This gives the ring `r` and the finite index type `I`. The closed inclusion of the
torus into the parabolic and its geometric-fibre maximality are retained by this
restriction. The Lean statement spells out this affine, standard-torus form. It is
a derived interface for the Borel-locus argument, rather than a verbatim additional
claim of the source.

## Scope and intended use

The base is arbitrary and all quantifiers have universe `u`. No Noetherian,
connectedness, reducedness, or chosen global torus hypothesis is added. The input
predicates are precisely `IsReductive` and `IsRelativeParabolicSubgroup`; the latter
requires smoothness, affineness, monomorphy, and parabolic residue fibres.

This statement supplies local coordinates in which the published local constancy
of adjoint weight dimensions can be applied to the parabolic. It makes no claim
that the Borel locus is open or closed.
