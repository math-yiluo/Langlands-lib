# Affine quotient sections from split-unipotent torsor triviality

This internal adapter retains `SplitUnipotentAffineTorsorStatement` as an
explicit hypothesis. Its main construction is an actual scheme section of
a supplied exact homogeneous quotient whose target is affine. It does not
prove the torsor statement or the full solvable maximal-torus conjugacy
theorem.

`HomogeneousQuotient.affine_lifts_of_split_unipotent_torsors` considers actual
group schemes `G` and `H` over any field, a monic homomorphism `i : H ⟶ G`,
and a supplied fpqc quotient map `q : G.X ⟶ Q`. Its fibers on every relative
scheme test are exactly right cosets of the range of `i`. If `H` is smooth,
affine and split unipotent, the torsor statement implies that every point
of `Q` over any affine test scheme `T` lifts to `G`.

The proof base changes the group, subgroup, quotient map and point to `T`.
The pullback adjunction and the existing subgroup base-change theorem
preserve the exact all-test coset condition. The existing
`Dynamic.flagQuotientFiber` construction supplies the actual fiber,
its lawful left action by the pulled-back subgroup, and its isomorphic
shear. Flatness, surjectivity and quasi-compactness follow by base change.
The assumed torsor statement gives a section of this fiber. Composing with
the fiber inclusion and applying the pullback adjunction yields the claimed
lift of the original point.

`affine_section_of_split_unipotent_torsors` applies the lifting theorem with
the affine quotient itself as test scheme and its identity as point.
`affineQuotientSection` chooses the resulting morphism `s : Q ⟶ G.X`;
`affineQuotientSection_comp` proves `s ≫ q = 𝟙 Q`, with its reassociated
version also available to simplification. The section is a morphism of
schemes over the field. It is not asserted to preserve multiplication.

`fppf_section_of_split_unipotent_torsors` specializes to an affine group
scheme `G`, a smooth closed split-unipotent subgroup `H`, and an affine
group scheme `K` supplied with a homomorphism `π : G ⟶ K` satisfying
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) π`. Closedness gives
the required monomorphism and affineness of `H`. The quotient predicate
gives flatness and surjectivity, and its exact represented kernel supplies
the all-test coset condition through `IsFppfQuotient.fibers_iff`.
Quasi-compactness of the projection follows from affineness of `G` over
the field: the composite projection followed by the structure map is
the structure map of `G`. Affineness of `K` over the affine field spectrum
gives affineness of its underlying scheme, so the preceding section
theorem applies.

This specialization needs no solvability or connectedness premise and no
smoothness premise on `G` or `K`; it retains the smoothness and split
unipotence of `H` and the supplied exact quotient. In particular, it can
provide the quotient-section step for solvable maximal-torus conjugacy
once the broader affine-torsor statement is proved.

The provenance is internal: this is a direct assembly of the existing
quotient-fiber action, subgroup base-change and pullback-adjunction interfaces.
No quotient existence, cohomology vanishing or structural group theorem is
proved here. No additional restriction on the field or the affine test
scheme is imposed.
