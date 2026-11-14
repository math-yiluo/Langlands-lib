# Fppf locality of group-scheme homomorphisms

This internal supporting result proves that equality of actual group-scheme
homomorphisms can be tested on a family of fppf neighborhoods through every
point of the base. Its purpose for the relative parabolic reductive quotient
problem is to descend the equation that a homomorphism annihilates the supplied
unipotent radical once that equation has been proved on etale neighborhoods.
It does not construct the neighborhoods, identify the radical there, or
construct a quotient.

## Statements

`Langlands.GroupScheme.PointwiseFppfHomEqualityStatement` quantifies over every
universe, scheme `S`, group schemes `G` and `H` over `S`, and two homomorphisms
`f, g : G ⟶ H`. For each point `s` of `S`, assume there is a scheme `T` and a
flat morphism `b : T ⟶ S` locally of finite presentation whose image contains
`s`, such that the actual pullbacks of `f` and `g` along `b` agree. Then `f = g`.
The theorem `pointwiseFppfHomEquality` proves this proposition.

The module also supplies these helpers:

- `hom_ext_of_baseChange_fppfCover` tests equality on any fppf covering family.
  Its index type may lie in a different universe from the schemes.
- `hom_ext_of_pointwise_fppf_baseChange` is the pointwise formulation used by
  the statement.
- `hom_ext_of_pointwise_etale_baseChange` specializes to etale neighborhoods.
- `comp_eq_zero_of_pointwise_etale_baseChange` proves `r ≫ f = 0` from the
  corresponding equations for the pullbacks of `r` and `f` on such neighborhoods.

No reducedness, affineness, smoothness, finite type, or quasi-compactness
assumption is imposed on the base or on the group schemes. Individual
neighborhood maps need not be surjective; their images together cover the base.

## Implemented proof and provenance

The provenance is internal: this is an application of Mathlib's subcanonical
fppf topology and actual scheme pullbacks, with no new literature assertion.
The imported `Mathlib.AlgebraicGeometry.Sites.Fpqc` proves subcanonicity of
`Scheme.fppfTopology`. The imported
`Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical` provides
`Precoverage.ZeroHypercover.hom_ext`, which reflects equality of morphisms
after precomposition with every member of a covering family for a subcanonical
topology.

First pull a base fppf cover back along the structure morphism of `G`. Equality
of base-changed homomorphisms gives equality after precomposition with each
projection to `G`, by the defining formula for a pullback map and its first
projection. Subcanonicity gives equality of the underlying scheme morphisms;
extensionality for morphisms over the base and group-object homomorphisms gives
the required equality.

For the pointwise version, choose one supplied neighborhood for each base
point. These morphisms form an fppf cover because they are flat, locally of
finite presentation, and jointly surjective. Apply the covering-family result.
Etale morphisms have the two required morphism properties. Preservation of
composition and the zero homomorphism by group-scheme base change gives the
zero-composite corollary. This proof detects actual scheme morphisms, including
over nonreduced bases; it does not use equality on geometric points or fibres.
