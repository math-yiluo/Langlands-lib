# The Leray spectral sequence on the small étale site

`Langlands.Cohomology.EtaleLeray.EtaleLerayStatement` concerns the small
étale sites of an actual morphism of schemes `f : X ⟶ S`. For a sheaf `F`
of modules over the constant commutative ring `R`, it states the first
quadrant spectral sequence with second page `H^i(S, R^j f_* F)` and
abutment `H^(i+j)(X, F)`. These comparisons are of underlying additive
groups. The two localizations for the derived categories of module sheaves
on `S` and `X` have independent universes.

The source is Milne, *Étale Cohomology* (1980), III.1, Theorem 1.18(a)
and Remark 1.20(a), printed pp. 89–90. The retained edition has literature
ID `milne-1980-etale-cohomology` and SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.
The module specializes the theorem to small étale sites and expresses it
through the canonical truncation sequence of the derived direct image.
The constant regular module sheaf represents the sections functor by the
constant sheaf adjunction. The derived direct image is bounded below,
and direct image preserves injectives because its left adjoint is exact.
The geometric comparison `directImageSectionsIso` identifies sections of
the direct image with sections over `X`. These identifications explain
the second page and the abutment of the specified covariant hyperext
sequence.

`FirstQuadrantAbutmentStatement` uses the finite decreasing truncation
filtration. In total degree `n` the filtration starts with the whole group
in step zero and ends with zero in step `n+1`. For bidegree `(i,j)` and
page `r ≥ max(2, i+1, j+2)`, both differentials at that bidegree vanish
and the group on that page is the associated graded group. The page and
abutment isomorphisms in this proposition are existence assertions.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (PDF p. 106), uses the sequence for
the structure map of a power of the universal abelian scheme after
geometric base change. Its retained edition has literature ID
`harris-taylor-2001-geometry-cohomology-simple-shimura` and SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Applying the comparison to the source's projected adic cohomology also
requires compatibility with the corresponding endomorphisms, coefficient
reductions and Galois action.
