# Original embedding coordinates are scalar-evaluation pullbacks

Author: Worker 166. This is an internal comparison of previously constructed
maps, derived from the actual affine-test formulas in
`AffineWeilEmbeddingEvaluation`. It uses no further source assertion.

For commutative rings `k`, `K`, and `Ω` with the given algebra structures,
finite embeddings and bijective canonical embedding evaluation, and an affine
group `H` locally of finite type over the finite projective `k`-algebra `K`,
`embeddingProductIsoOfBijective_hom_π` proves that each original factor
projection of the actual Weil-product isomorphism is the actual pullback
component of scalar evaluation `W_K → H`. The base map is the original
embedding on spectra, and all group-scheme maps are the existing maps.

The proof begins with the established equality after the multiplicative factor
point comparison. `embeddingProductCoordinatePoint` and
`embeddingEvaluationPoint` give the two coordinate points explicit identical
types. `embeddingProductCoordinatePoint_compared` restates the established
comparison with these definitions, and `embeddingProductCoordinatePoint_eq`
uses injectivity of the original factor point equivalence.

The definitions `embeddingProductCoordinateOverHom` and
`embeddingEvaluationOverHom` retain the underlying morphisms over the base.
Their defining equations identify them with the original maps. The two point
application formulas then translate the point equality to equality on every
affine test. Testing on the canonical affine presentation of the source proves
`embeddingProductCoordinateOverHom_eq_evaluation`. Finally, the original
composition formula and extensionality for group-object homomorphisms prove
`embeddingProductIsoOfBijective_hom_π`.

The explicitly typed point and morphism definitions control definitional
reduction; they do not change any map or hypothesis. The module proves the
coordinate-morphism identity. Canonical Galois compatibility and the main
simply connected structural theorem remain downstream.
