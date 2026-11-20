# A finite carrier for every prescribed generic outer class

`Langlands.GroupScheme.finiteGenericOuterClassExistence` proves
`Langlands.GroupScheme.FiniteGenericOuterClassExistenceStatement.{u}` for every
universe `u`.

The proof intersects the affine pinned étale atlases for `G` and `H` to
obtain a common covering family. On a pairwise fibre product, the two
pullback comparisons identify the restricted groups with the corresponding
pinned models after base change. The pinned chart theorem gives a constant
family of normalized representatives in the pullback of the supplied
isomorphism scheme `I`. Its orbit bijection is for the inner action of the
supplied full-centre adjoint quotient. The action base-change identity and
the local-section comparison transfer this bijection to the tests over
`Spec R`.

`OuterIsomorphismScheme.geometry_of_localConstants` supplies separatedness
and an actual constant trivialization on each cover member for the given
outer quotient `O`. The smoothness of the adjoint target follows from
reductivity and provides the flatness and local finite presentation
required for this comparison.

`FiniteGenericOuterClass.ofEtaleCover` uses a cover member meeting the closed
point and extends the generic class to a section of `O.parameter`. The base
scheme, finite over itself, serves as the carrier. The construction takes
`p` to be the point of `I.parameter` classified by the natural local
family of the prescribed isomorphism `f`. The carrier's generic point maps
to the image of `p` under `O.classMap`.

This is an internal composition of the published pinned chart
classification, the supplied-quotient geometry comparison and the
étale descent construction for a generic section. Its mathematical
provenance is the local constancy and extension argument in Brian Conrad,
*Reductive group schemes* (2014), Theorem 7.1.9(1) and its proof on
pp. 245–247, and the forms argument in Theorem 7.2.16 on p. 261.
The source is registered as `conrad-2014-reductive-group-schemes` with
SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
