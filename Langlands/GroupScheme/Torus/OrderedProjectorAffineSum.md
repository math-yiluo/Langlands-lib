# Disjoint affine opens in the moduli of subtori of a general linear group

Fix an affine base `Spec R`, a finite matrix index `n` with decidable equality,
and a parameter scheme `M` over `Spec R`. Suppose `M` carries a relative torus
`K` and an inclusion `j` into the pullback of `GL_n` to `M.left`. The assumptions
are `IsClosedSubgroup j`, `RelativeTorus.IsTorus K`, and
`TorusSubgroupModuli.IsUniversal j`, so `j` classifies the closed torus
subgroups on every test over `Spec R`. Under these hypotheses,
`exists_disjoint_affineOpen_cover` gives a cover of `M.left` by pairwise
disjoint affine opens.

If two chart images meet, a common point lifts to the scheme-theoretic overlap. The overlap is a coproduct indexed by matchings of the ordered weights. The summand containing the lifted point supplies a matching, and relabelling by that matching and its inverse gives both inclusions between the images.

`ChartImageIndex` indexes the distinct open images of the split charts. Each
chart is affine over `Spec R` and maps finitely and surjectively to its open
image, so that image is affine. The étale local coverage theorem supplies a
chart image containing each point of `M.left`.
