# Proper finitely presented algebraic spaces admit proper scheme covers

`ProperSchemeCoverStatement` is a derived prerequisite for properness descent,
not a proof. For an affine scheme S and an algebraic space X over S, it assumes
relative quasi-separatedness, a quasi-compact locally finitely presented etale
surjective atlas, and properness of the actual structural morphism. It asks
for a scheme U over S with a surjective represented morphism to X, such that
U's structural scheme morphism is proper and locally finitely presented.

Surjectivity is the existing relative `IsSurjective` predicate: every represented
pullback projection is a surjective scheme morphism. The cover is not assumed
etale, and X is not assumed represented by a scheme. Properness and local finite
presentation of U over S in particular give a quasi-compact quasi-separated
finite-presentation scheme model suitable for the existing scheme limit theorems.

The source is the registered Stacks Project folder
`stacks-proper-scheme-covers-2026-11-11`, files `089I.html`, `088S.html` and
`089L.html`. Section 69.18, Lemma 69.18.1 (Tag 089I) gives a proper surjective
scheme cover of a separated finite type algebraic space over an affine base.
Lemma 76.40.3 (Tag 088S) gives the Noetherian cover construction, while Lemma
76.41.1 (Tag 089L), especially its second proof paragraph, reduces an arbitrary
finitely presented separated morphism to a separated finite type morphism
over a Noetherian base. Neither explicit cover conclusion by itself asserts
the finite-presentation refinement in this interface.

The refinement has the following intended derivation. Approximate the given
finitely presented algebraic space over an affine base by a model over a
Noetherian affine base and arrange separatedness there, using model existence
and separatedness descent. A proper surjective scheme cover of this
Noetherian model is of finite presentation. Pull it back to the original
space. Its source remains a scheme, the cover remains proper and surjective,
and its structural morphism is locally finitely presented. Since the original
space is proper over S, the source scheme is proper over S by composition.
This route uses separatedness descent, but does not assume properness descent.
The formal proof, including the approximation, compatibility and actual cover
construction, remains an obligation of the prerequisite proof task.

This statement contains no limit diagram and asserts no property of a stage
model. Its consumer is the forward universal-closedness portion of
`SpaceLimitPropertyDescentStatement`: descend the actual proper scheme cover
and its morphism to an incoming stage, detect surjectivity there, and use the
proper source to establish universal closedness. Those consumer steps and the
full eight-property theorem remain with the host task.
