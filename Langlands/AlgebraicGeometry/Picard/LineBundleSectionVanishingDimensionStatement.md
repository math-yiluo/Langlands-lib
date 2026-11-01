# Dimension of the actual vanishing locus of a line-bundle section

`LineBundleSectionVanishingDimensionStatement` concerns an actual scheme
`X` smooth of relative dimension `g` over an arbitrary field `K`, proper
and geometrically connected over that field. For every actual line bundle
`L` and global section `s`, suppose its whole generation open contains a
point and has a point outside it. Then the topological Krull dimension of
the complement of that open, plus one, equals `g`. Dimensions take values
in `WithBot ℕ∞`.

The generation open is the published `trivializationOpen L.obj s`, the
whole locus where the section gives a frame of the line bundle. The
vanishing locus here is its actual set complement with its subspace
topology. No choice of a zero subscheme is part of the statement. No
algebraic-closure or characteristic hypothesis is imposed, and no
ampleness hypothesis is needed once the section and its two nonemptiness
conditions are given.

This is an internal geometric consequence of published smooth geometric
integrality, the bound on global smooth dimension, closed-point stalk
dimension, and the local principal quotient inequality. Smooth geometric
integrality makes the generation open dense. Its proper closed complement
has dimension plus one at most `g`. At a closed point in that complement,
a local frame expresses the section as one nonunit coefficient. The
spectrum of the local quotient embeds in the actual vanishing locus;
the local principal quotient inequality gives the reverse bound.

This preparation establishes the first cut's topological dimension in the
smooth case. It asserts no smoothness of the vanishing locus, no recursive
singular cut formula, no Euler polynomial, and no leading-coefficient
positivity.
