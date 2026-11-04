# Actual rational-point central character

Worker 101 constructs the central character of any irreducible smooth complex
representation of the actual rational points of a connected reductive group over
any nonarchimedean local field. The field universe `u` and representation-carrier
universe `uV` are independent. The topology is exactly
`rationalPointTopology F G.X`.

This is an internal construction for the scalar-centre step of Renard VI.3.2(ii),
not a separately numbered proposition in the source. Its motivation is David
Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.3.2(ii), printed pp.143–144 / PDF pp.149–150. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passage was read in full; no project errata record was found.

`exists_scalar_rationalPoint_center` proves that every element of the centre of
the actual rational-point group acts by a complex scalar. The local field is
second countable by the published general local-field theorem. Smoothness of the
connected reductive group supplies local finite type. The published
finite-coordinate theorem makes its affine point space second countable, and
the published affine/rational-point homeomorphism transports that property to
the canonical rational-point topology. The canonical topology is a group
topology. The published smooth orbit argument therefore bounds the algebraic
dimension of the irreducible representation by `Cardinal.aleph0`. Published
countable-dimensional Schur, applied to the action of a central element, gives
the scalar. These deductions do not require admissibility.

`rationalPointCentralCharacter F G hG π hπ` returns a subtype whose value is an
actual homomorphism
`Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ`, and whose property is
`π.HasCentralCharacter` for that homomorphism. This property refers to the
original action `π.representation` on every vector. Choose scalars from the
existence theorem and choose a nonzero vector using irreducibility. Evaluating
on that vector proves the identity and multiplication laws. The scalar of an
element is nonzero because its product with the scalar of its inverse is one.
The resulting units form the returned monoid homomorphism, with the scalar
action supplied by the original chosen equalities.
