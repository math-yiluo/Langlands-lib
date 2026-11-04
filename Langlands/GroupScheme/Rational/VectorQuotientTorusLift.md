# Actual torus lifts through vector quotients

This internal construction supplies homomorphic torus lifts for a flat,
surjective morphism `q : G ⟶ Q` of group schemes, with `G` affine, over
any field `k : Type u`. Its kernel is presented by a homomorphism `n : V ⟶ G`
whose underlying relative scheme map is monic, with equality
`range n = range (kernelι q)` on every scheme test, and by
`IsVectorGroupOfDimension V d`. The dimension may be zero.

`SubgroupPreimage.isVectorGroupOfDimension_kernel` applies to any
homomorphism `j : H ⟶ Q`. The full kernel presentation identifies `V`
with the actual kernel of `q` through the published represented-subgroup
comparison. The published `SubgroupPreimage.kernelIso` identifies the
kernel of the inverse-image projection with that original kernel.
Transport of natural vector coordinates along the composite isomorphism
gives the same dimension `d` for the inverse-image kernel. This conclusion
uses no torus, closedness, flatness or surjectivity hypothesis.

For the lift construction, `j` is a closed subgroup homomorphism and
`IsTorus H` uses the existing arbitrary-torus predicate.
`IsTorus.exists_vectorQuotientLift` proves existence of an actual
group-scheme homomorphism `l : H ⟶ G` with `l ≫ q = j`.
The theorem retains the exact proposition
`TorusVectorActionLinearizationStatement.{u}` as an explicit input.
It does not assume a scheme section or any additional linear coordinate
system.

The implemented proof forms the actual group-scheme pullback
`SubgroupPreimage.groupScheme q j`. Its projection to `H` is flat and
surjective by base change. Its inclusion into `G` is closed by base change
of `j`, so it is affine over `k`. The torus `H` is also affine.
The preceding kernel comparison supplies the vector presentation for
the actual kernel inclusion of this projection. The imported
`IsTorus.exists_vectorExtensionSection` produces a homomorphic section
over `k`. Composing that section with the pullback inclusion into `G`
gives the required lift; the pullback commutativity identity proves its
exact composite with `q`.

`IsTorus.vectorQuotientLift` chooses the homomorphism from this existence
theorem. `vectorQuotientLift_comp` proves its equality with the specified
map `j` after composition with `q`.

The provenance is internal: the result combines published pullback,
represented-subgroup and coordinate-transport constructions with the
vector-extension section construction. It imposes no characteristic,
perfection, field cardinality, splitting or positive-dimension
restriction. It does not prove torus-action linearization, splitting of
extensions by general split unipotent groups, or maximal-torus conjugacy.
